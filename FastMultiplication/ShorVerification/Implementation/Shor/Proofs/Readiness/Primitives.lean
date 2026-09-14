import FastMultiplication.ShorVerification.Implementation.Shor.Circuit.OrderFinding
import FastMultiplication.ShorVerification.Implementation.Shor.Spec.Setup
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Lowering
import FastMultiplication.ShorVerification.Implementation.QFT.Proofs.Lowering.Readiness
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Proofs.Core
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Proofs.ConstArithmetic
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Workspace
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Circuit.Steps
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Lowering.ConstArithmetic
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Spec.Validity
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Workspace
import FastMultiplication.ShorVerification.Implementation.Shared.States
import FastMultiplication.ShorVerification.Implementation.Shared.Registers
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Static
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Readiness.Sequencing

/-!
# Primitive Locality and Step 3/4 Readiness

Two parts. First, workspace-free gates: gate constructors with no recursive
lowerer workspace obligations, culminating in `WorkspaceFree.clean`, which
turns that syntactic fact into `GateWorkspaceCleanState`. Second, primitive
register-locality/disjointness helpers and the readiness/clean-state
preservation proofs for Steps 3 and 4 (the concrete comparator and its
constant-arithmetic lowering), culminating in `lowered_step3_ready_and_clean`.
-/

namespace Shor
open Gate
open Classical

/-! =========================================================
    Workspace-free gates

    These gates have no recursive lowerer workspace obligations. The final
    helper of this section, `WorkspaceFree.clean`, turns that syntactic fact
    into `GateWorkspaceCleanState`.
========================================================= -/

/--
A gate whose syntax contains no QFT or recursive phase-product nodes.

Such gates have no dynamic lowering-workspace cleanliness obligations.
-/
inductive WorkspaceFree : Gate → Prop
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


theorem WorkspaceFree.clean
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
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
                lowering.k
                lowering.hk
                lowering.ops
                U
                hworkspace.1)
              ψ)⟩

lemma workspaceFree_H_reg
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

lemma workspaceFree_initY1
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
    Primitive locality and Step 3/4 readiness

    The disjointness helpers feed the primitive semantic locality assumptions
    for Steps 3 and 4. The final theorems in this section are
    `lowered_step3_ready_and_clean` and `lowered_step4_ready_and_clean`.
========================================================= -/

lemma reserve_active_disjoint_of_ownedDisjoint
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

lemma ownedDisjoint_symm
    {x y : ExtReg}
    (hxy :
      ExtReg.OwnedDisjoint x y) :
    ExtReg.OwnedDisjoint y x := by
  exact List.Disjoint.symm hxy

lemma disjoint_qubitReg_of_mem_right
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

lemma reserve_drop_active_disjoint_of_ownedDisjoint
    {x y : ExtReg}
    (hxy :
      ExtReg.OwnedDisjoint x y)
    (n : ℕ) :
    Disjoint (x.reserve.drop n) y.active :=
  disjoint_drop_left
    (reserve_active_disjoint_of_ownedDisjoint hxy)
    n

lemma reserve_drop_active_disjoint_self
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
lemma not_mem_right_of_mem_left_of_disjoint
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
    (x data work scratch : ExtReg)
    (N flag : ℕ)
    (hxData :
      ExtReg.OwnedDisjoint x data)
    (hxScratch :
      ExtReg.OwnedDisjoint x scratch)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (hflagX :
      flag ∉ x.ownedQubits)
    (hstep4 :
      CmpLtNWWorkspace N (data.grow 1) work scratch flag)
    {ψ : qs.State}
    (hclean :
      ShorConcreteCleanState
        qs x data work scratch hxScratch ψ) :
    ShorConcreteCleanState
      qs x data work scratch hxScratch
      (qs.eval
        (step3
          N
          (data.grow 1)
          scratch
          flag)
        ψ) := by
  have hxCarry :
      Disjoint x.reserve (data.grow 1).active :=
    reserve_grow_active_disjoint_of_ownedDisjoint hxData 1

  have hdataCarry :
      Disjoint (data.reserve.drop 1) (data.grow 1).active :=
    reserve_drop_grow_active_disjoint_self data 1

  have hworkCarry :
      Disjoint work.reserve (data.grow 1).active :=
    reserve_active_disjoint_of_ownedDisjoint
      hmod.work_dataCarry_disjoint

  have hcombinedCarry :
      Disjoint
        (exponentScratchCleanReg x scratch hxScratch)
        (data.grow 1).active := by
    rw [Disjoint, List.disjoint_left]
    intro q hqCombined hqCarry
    simp only [
      exponentScratchCleanReg,
      Reg.append,
      ExtReg.ownedReg,
      List.mem_append
    ] at hqCombined
    rcases hqCombined with hqExponent | hqScratch
    · exact
        (not_mem_right_of_mem_left_of_disjoint
          hxCarry hqExponent) hqCarry
    · have hscratchCarry := hstep4.data_scratch_disjoint
      rw [ExtReg.OwnedDisjoint, List.disjoint_left] at hscratchCarry
      exact hscratchCarry
        (List.mem_append_left _ hqCarry)
        (by simpa [ExtReg.ownedQubits] using hqScratch)

  have hflagCombined :
      flag ∉
        (exponentScratchCleanReg x scratch hxScratch).qubits := by
    intro hqCombined
    simp only [
      exponentScratchCleanReg,
      Reg.append,
      ExtReg.ownedReg,
      List.mem_append
    ] at hqCombined
    rcases hqCombined with hqExponent | hqScratch
    · apply hflagX
      rw [ExtReg.ownedQubits, List.mem_append]
      exact Or.inr hqExponent
    · exact hstep4.flag_not_scratch
        (by simpa [ExtReg.ownedQubits] using hqScratch)

  induction hclean with
  | zero =>
      rw [qs.eval_zero]
      exact ThreeRegsCleanState.zero

  | ket b hbasis =>
      rcases hbasis with ⟨hcombined, hdata, hwork⟩
      rcases
          eval_step3_local_ket
            (qs := qs)
            N
            (data.grow 1)
            scratch
            flag
            b
            (by
              intro hq
              apply hstep4.flag_not_data
              have howned :
                  flag ∈ (data.grow 1).ownedQubits :=
                List.mem_append_left _ hq
              simpa [Gate.ExtReg.ownedQubits_grow] using howned) with
        ⟨b', heval, hlocal⟩

      rw [heval]
      apply ThreeRegsCleanState.ket

      · exact
          FreshZero.of_eq_on_bits
            (exponentScratchCleanReg x scratch hxScratch)
            b
            b'
            (by
              intro q hq
              apply hlocal q
              · exact
                  not_mem_right_of_mem_left_of_disjoint
                    hcombinedCarry hq
              · intro hqFlag
                subst q
                exact hflagCombined hq)
            hcombined

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
                apply hstep4.flag_not_data
                rw [ExtReg.ownedQubits, List.mem_append]
                exact Or.inr hq)
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
                apply hstep4.flag_not_work
                rw [ExtReg.ownedQubits, List.mem_append]
                exact Or.inr hq)
            hwork

  | add hψ hφ ihψ ihφ =>
      rw [qs.eval_add]
      exact ThreeRegsCleanState.add ihψ ihφ

  | smul a hψ ihψ =>
      rw [qs.eval_smul]
      exact ThreeRegsCleanState.smul a ihψ
theorem eval_step4_preserves_lowering_clean
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (x data work scratch : ExtReg)
    (N flag : ℕ)
    (hxData :
      ExtReg.OwnedDisjoint x data)
    (hxWork :
      ExtReg.OwnedDisjoint x work)
    (hxScratch :
      ExtReg.OwnedDisjoint x scratch)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (hflagX :
      flag ∉ x.ownedQubits)
    (hstep4 :
      CmpLtNWWorkspace N (data.grow 1) work scratch flag)
    {ψ : qs.State}
    (hclean :
      ShorConcreteCleanState
        qs x data work scratch hxScratch ψ) :
    ShorConcreteCleanState
      qs x data work scratch hxScratch
      (qs.eval
        (step4
          N
          (data.grow 1)
          work
          scratch
          flag
          hstep4)
        ψ) := by
  have hxCarry :
      Disjoint x.reserve (data.grow 1).active :=
    reserve_grow_active_disjoint_of_ownedDisjoint hxData 1

  have hxWorkActive :
      Disjoint x.reserve work.active :=
    reserve_active_disjoint_of_ownedDisjoint hxWork

  have hdataCarry :
      Disjoint (data.reserve.drop 1) (data.grow 1).active :=
    reserve_drop_grow_active_disjoint_self data 1

  have hdataWorkActive :
      Disjoint (data.reserve.drop 1) work.active :=
    reserve_drop_active_disjoint_of_ownedDisjoint hmod.2.2 1

  have hworkCarry :
      Disjoint work.reserve (data.grow 1).active :=
    reserve_active_disjoint_of_ownedDisjoint
      hmod.work_dataCarry_disjoint

  have hworkWorkActive :
      Disjoint work.reserve work.active :=
    Disjoint.symm work.active_reserve_disjoint

  have hcombinedCarry :
      Disjoint
        (exponentScratchCleanReg x scratch hxScratch)
        (data.grow 1).active := by
    rw [Disjoint, List.disjoint_left]
    intro q hqCombined hqCarry
    simp only [
      exponentScratchCleanReg,
      Reg.append,
      ExtReg.ownedReg,
      List.mem_append
    ] at hqCombined
    rcases hqCombined with hqExponent | hqScratch
    · exact
        (not_mem_right_of_mem_left_of_disjoint
          hxCarry hqExponent) hqCarry
    · have hscratchCarry := hstep4.data_scratch_disjoint
      rw [ExtReg.OwnedDisjoint, List.disjoint_left] at hscratchCarry
      exact hscratchCarry
        (List.mem_append_left _ hqCarry)
        (by simpa [ExtReg.ownedQubits] using hqScratch)

  have hcombinedWork :
      Disjoint
        (exponentScratchCleanReg x scratch hxScratch)
        work.active := by
    rw [Disjoint, List.disjoint_left]
    intro q hqCombined hqWork
    simp only [
      exponentScratchCleanReg,
      Reg.append,
      ExtReg.ownedReg,
      List.mem_append
    ] at hqCombined
    rcases hqCombined with hqExponent | hqScratch
    · exact
        (not_mem_right_of_mem_left_of_disjoint
          hxWorkActive hqExponent) hqWork
    · have hworkScratch := hstep4.work_scratch_disjoint
      rw [ExtReg.OwnedDisjoint, List.disjoint_left] at hworkScratch
      exact hworkScratch
        (List.mem_append_left _ hqWork)
        (by simpa [ExtReg.ownedQubits] using hqScratch)

  have hflagCombined :
      flag ∉
        (exponentScratchCleanReg x scratch hxScratch).qubits := by
    intro hqCombined
    simp only [
      exponentScratchCleanReg,
      Reg.append,
      ExtReg.ownedReg,
      List.mem_append
    ] at hqCombined
    rcases hqCombined with hqExponent | hqScratch
    · apply hflagX
      rw [ExtReg.ownedQubits, List.mem_append]
      exact Or.inr hqExponent
    · exact hstep4.flag_not_scratch
        (by simpa [ExtReg.ownedQubits] using hqScratch)

  induction hclean with
  | zero =>
      rw [qs.eval_zero]
      exact ThreeRegsCleanState.zero

  | ket b hbasis =>
      rcases hbasis with ⟨hcombined, hdata, hwork⟩
      have hdataFresh : (data.grow 1).FreshFor 1 b := by
        unfold ExtReg.FreshFor
        apply FreshZero.of_subset
            ((data.grow 1).newBits 1)
            (data.reserve.drop 1)
            b
        · intro q hq
          simpa [ExtReg.grow, ExtReg.newBits, ExtReg.remainingReserve,
            Reg.take, Reg.drop] using List.mem_of_mem_take hq
        · exact hdata
      have hworkFresh : work.FreshFor 1 b := by
        unfold ExtReg.FreshFor
        apply FreshZero.of_subset (work.newBits 1) work.reserve b
        · intro q hq
          exact List.mem_of_mem_take hq
        · exact hwork
      have hscratchZero :
          RegEncoding.toNat scratch.active b = 0 := by
        apply FreshZero.of_subset
            scratch.active
            (exponentScratchCleanReg x scratch hxScratch)
            b
        · intro q hq
          simp only [
            exponentScratchCleanReg,
            Reg.append,
            ExtReg.ownedReg,
            List.mem_append
          ]
          exact Or.inr (Or.inl hq)
        · exact hcombined
      have hscratchFresh : scratch.FreshFor 1 b := by
        unfold ExtReg.FreshFor
        apply FreshZero.of_subset
            (scratch.newBits 1)
            (exponentScratchCleanReg x scratch hxScratch)
            b
        · intro q hq
          simp only [
            exponentScratchCleanReg,
            Reg.append,
            ExtReg.ownedReg,
            List.mem_append
          ]
          exact Or.inr (Or.inr (List.mem_of_mem_take hq))
        · exact hcombined
      rcases
          eval_step4_local_ket
            (qs := qs)
            N
            (data.grow 1)
            work
            scratch
            flag
            hstep4
            b
            hdataFresh
            hworkFresh
            hscratchZero
            hscratchFresh with
        ⟨b', heval, hlocal⟩

      rw [heval]
      apply ThreeRegsCleanState.ket

      · exact
          FreshZero.of_eq_on_bits
            (exponentScratchCleanReg x scratch hxScratch)
            b
            b'
            (by
              intro q hq
              apply hlocal q
              · exact
                  not_mem_right_of_mem_left_of_disjoint
                    hcombinedCarry hq
              · exact
                  not_mem_right_of_mem_left_of_disjoint
                    hcombinedWork hq
              · intro hqFlag
                subst q
                exact hflagCombined hq)
            hcombined

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
                apply hstep4.flag_not_data
                rw [ExtReg.ownedQubits, List.mem_append]
                exact Or.inr hq)
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
                apply hstep4.flag_not_work
                rw [ExtReg.ownedQubits, List.mem_append]
                exact Or.inr hq)
            hwork

  | add hψ hφ ihψ ihφ =>
      rw [qs.eval_add]
      exact ThreeRegsCleanState.add ihψ ihφ

  | smul a hψ ihψ =>
      rw [qs.eval_smul]
      exact ThreeRegsCleanState.smul a ihψ

private theorem shorConcreteCleanState_to_constArithmeticCleanState
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    (x data work scratch : ExtReg)
    (hxScratch : x.OwnedDisjoint scratch)
    {ψ : qs.State}
    (hclean :
      ShorConcreteCleanState
        qs x data work scratch hxScratch ψ) :
    CmpGeConstCleanState qs (data.grow 1) scratch ψ := by
  induction hclean with
  | zero => exact CleanClosure.zero
  | ket b hbasis =>
      rcases hbasis with ⟨hcombined, hdata, hwork⟩
      apply CleanClosure.ket
      refine ⟨?_, ?_, ?_⟩
      · unfold ExtReg.FreshFor
        apply FreshZero.of_subset
            ((data.grow 1).newBits 1)
            (data.reserve.drop 1)
            b
        · intro q hq
          simpa [ExtReg.grow, ExtReg.newBits, ExtReg.remainingReserve,
            Reg.take, Reg.drop] using List.mem_of_mem_take hq
        · exact hdata
      · have hscratchZero :
            RegEncoding.toNat scratch.active b = 0 := by
          apply FreshZero.of_subset
              scratch.active
              (exponentScratchCleanReg x scratch hxScratch)
              b
          · intro q hq
            simp only [
              exponentScratchCleanReg,
              Reg.append,
              ExtReg.ownedReg,
              List.mem_append
            ]
            exact Or.inr (Or.inl hq)
          · exact hcombined
        rw [extToInt, ExtReg.toNat, hscratchZero]
        cases scratch.width <;> simp [tcDecodeWidth]
      · unfold ExtReg.FreshFor
        apply FreshZero.of_subset
            (scratch.newBits 1)
            (exponentScratchCleanReg x scratch hxScratch)
            b
        · intro q hq
          simp only [
            exponentScratchCleanReg,
            Reg.append,
            ExtReg.ownedReg,
            List.mem_append
          ]
          exact Or.inr (Or.inr (List.mem_of_mem_take hq))
        · exact hcombined
  | add hψ hφ ihψ ihφ => exact CleanClosure.add ihψ ihφ
  | smul a hψ ihψ => exact CleanClosure.smul a ihψ

theorem lowered_step3_ready_and_clean
    {qs : QSemantics}
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    (lowering : ShorLoweringSetup)
    (x data work scratch : ExtReg)
    (N flag : ℕ)
    (hxData :
      ExtReg.OwnedDisjoint x data)
    (hxScratch :
      ExtReg.OwnedDisjoint x scratch)
    (hmod :
      ModMulCircuitWorkspaceOK data work)
    (hflagX :
      flag ∉ x.ownedQubits)
    (hstep4 :
      CmpLtNWWorkspace N (data.grow 1) work scratch flag)
    (hworkspace :
      GateWorkspaceOK
        lowering.ops
        (step3 N (data.grow 1) scratch flag))
    (ψ : qs.State)
    (hclean :
      ShorConcreteCleanState
        qs x data work scratch hxScratch ψ) :
    LoweredCleanResult
      qs
      lowering
      (ShorConcreteCleanState
        qs x data work scratch hxScratch)
      (step3 N (data.grow 1) scratch flag)
      hworkspace
      ψ := by
  have hcmpClean :
      CmpGeConstCleanState
        qs (data.grow 1) scratch ψ :=
    shorConcreteCleanState_to_constArithmeticCleanState
      x data work scratch hxScratch hclean

  have hgateClean :
      GateWorkspaceCleanState
        qs
        lowering.k
        lowering.hk
        lowering.ops
        (step3 N (data.grow 1) scratch flag)
        hworkspace
        ψ := by
    change
      CmpGeConstCleanState qs (data.grow 1) scratch ψ ∧
      CSubConstCleanState qs N (data.grow 1) scratch flag
        (LowerGateClass.evalL (qs := qs)
          (lowerCmpGeConst N (data.grow 1) scratch flag hworkspace.1) ψ)
    refine ⟨hcmpClean, ?_⟩
    simpa [CSubConstCleanState, CSubConstCleanBasis] using
      evalL_lowerCmpGeConst_preserves_clean
        N (data.grow 1) scratch flag hworkspace.1 ψ hcmpClean

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
        (step3 N (data.grow 1) scratch flag)
        hworkspace
        ψ
        hgateClean
    ]
    exact
      eval_step3_preserves_lowering_clean
        x data work scratch N flag
        hxData hxScratch hmod hflagX hstep4 hclean

end Shor
