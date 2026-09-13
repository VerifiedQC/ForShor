import FastMultiplication.ShorVerification.Framework.Semantics.GateSemantics
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Gates.Macros
import FastMultiplication.ShorVerification.Implementation.Semantics.GateSemanticsLemmas

/-!
# Modular-Exponentiation Circuit Workspace

The static workspace structures consumed by the concrete Algorithm-1 circuit:
`ModMulCircuitWorkspaceOK` (the phase-product reserves needed by Steps 1, 2,
and 5), `CmpLtNWWorkspace` (Step 4's comparator workspace, plus the width
formula `cmpLtNWWidth` it is defined against), `ConstArithmeticWorkspace`
(the concrete lowering of Step 3's constant arithmetic), and `ModMulCoreLayout`
(the static register/qubit-disjointness layout every core invocation needs).
-/

namespace Shor

open Gate

/--
Layout assumptions for one invocation of `CmodMulInPlaceCore`.

`data.grow 1` is used because Algorithm 1 temporarily activates one reserve
bit of `data` as its carry/high bit.
-/
def ModMulCoreLayout (data work : ExtReg) (flag ctrl : ℕ) : Prop :=
  ExtReg.OwnedDisjoint data work ∧
  flag ∉ data.ownedQubits ∧
  flag ∉ work.ownedQubits ∧
  ctrl ∉ data.ownedQubits ∧
  ctrl ∉ work.ownedQubits ∧
  ctrl ≠ flag

/-- Static workspace condition for one controlled modular-multiplication core. -/
def ModMulCircuitWorkspaceOK (data work : ExtReg) : Prop :=
  data.CanGrow 2 ∧ work.CanGrow 1 ∧ ExtReg.OwnedDisjoint data work

lemma ModMulCircuitWorkspaceOK.data_canGrow_one
    {data work : ExtReg} (h : ModMulCircuitWorkspaceOK data work) : data.CanGrow 1 := by
  unfold ModMulCircuitWorkspaceOK at h
  unfold ExtReg.CanGrow ExtReg.capacity at *
  omega

lemma ModMulCircuitWorkspaceOK.dataCarry_canGrow_one
    {data work : ExtReg} (h : ModMulCircuitWorkspaceOK data work) : (data.grow 1).CanGrow 1 := by
  have h1 : data.CanGrow 1 := h.data_canGrow_one
  unfold ModMulCircuitWorkspaceOK at h
  rw [ExtReg.CanGrow, ExtReg.capacity_grow data 1 h1]
  unfold ExtReg.CanGrow ExtReg.capacity at h
  simp [ExtReg.CanGrow, ExtReg.capacity] at *
  omega

lemma ModMulCircuitWorkspaceOK.work_canGrow_one
    {data work : ExtReg} (h : ModMulCircuitWorkspaceOK data work) : work.CanGrow 1 :=
  h.2.1

lemma ModMulCircuitWorkspaceOK.dataCarry_work_disjoint
    {data work : ExtReg} (h : ModMulCircuitWorkspaceOK data work) :
    ExtReg.OwnedDisjoint (data.grow 1) work := by
  unfold ModMulCircuitWorkspaceOK at h
  unfold ExtReg.OwnedDisjoint at h ⊢
  rw [List.disjoint_left]
  intro q hqGrow hqWork
  simp [ExtReg.ownedQubits, ExtReg.grow, Reg.append,
    ExtReg.newBits, ExtReg.remainingReserve, Reg.take, Reg.drop,
    List.mem_append] at hqGrow
  have hqData : q ∈ data.ownedQubits := by
    rw [ExtReg.ownedQubits, List.mem_append]
    rcases hqGrow with hqActive | hqReserve
    · exact Or.inl hqActive
    · rcases hqReserve with hqNew | hqRemaining
      · exact Or.inr (List.mem_of_mem_take hqNew)
      · exact Or.inr (List.tail_subset _ hqRemaining)
  exact h.2.2 hqData hqWork

lemma ModMulCircuitWorkspaceOK.work_dataCarry_disjoint
    {data work : ExtReg} (h : ModMulCircuitWorkspaceOK data work) :
    ExtReg.OwnedDisjoint work (data.grow 1) := by
  exact List.Disjoint.symm h.dataCarry_work_disjoint

/-- The PhaseProduct workspace used by Step 1. -/
def ModMulCircuitWorkspaceOK.step1Workspace
    {data work : ExtReg} (h : ModMulCircuitWorkspaceOK data work) :
    Gate.PhaseProdWorkspace data.active work.active :=
  let dataNoCarry : ExtReg :=
    ExtReg.withReserve
      data.active
      (data.reserve.drop 1)
      (by
        rw [Disjoint, List.disjoint_left]
        intro q hqActive hqReserve
        have hdisj := data.active_reserve_disjoint
        rw [Disjoint, List.disjoint_left] at hdisj
        exact hdisj hqActive (List.mem_of_mem_drop hqReserve))
  Gate.PhaseProdWorkspace.ofExtRegs
    dataNoCarry work
    (by
      dsimp [dataNoCarry]
      unfold ExtReg.CanGrow ExtReg.capacity
      change 1 ≤ regSize (data.reserve.drop 1)
      simp [Reg.drop, regSize, Reg.width]
      change 1 ≤ regSize data.reserve - 1
      have hdata2 : 2 ≤ regSize data.reserve := by
        simpa [ExtReg.CanGrow, ExtReg.capacity] using h.1
      omega)
    h.work_canGrow_one
    (by
      unfold ExtReg.OwnedDisjoint
      rw [List.disjoint_left]
      intro q hqData hqWork
      apply h.2.2
      · rw [ExtReg.ownedQubits, List.mem_append] at hqData ⊢
        rcases hqData with hqActive | hqReserve
        · exact Or.inl hqActive
        · exact Or.inr (List.mem_of_mem_drop hqReserve)
      · exact hqWork)

/-- The PhaseProduct workspace used by Step 2, after growing the data register by one carry bit. -/
def ModMulCircuitWorkspaceOK.step2Workspace
    {data work : ExtReg} (h : ModMulCircuitWorkspaceOK data work) :
    Gate.PhaseProdWorkspace work.active (data.grow 1).active :=
  Gate.PhaseProdWorkspace.ofExtRegs
    work (data.grow 1) h.work_canGrow_one h.dataCarry_canGrow_one h.work_dataCarry_disjoint

/-- The PhaseProduct workspace used by Step 5. -/
def ModMulCircuitWorkspaceOK.step5Workspace
    {data work : ExtReg} (h : ModMulCircuitWorkspaceOK data work) :
    Gate.PhaseProdWorkspace (data.grow 1).active work.active :=
  Gate.PhaseProdWorkspace.ofExtRegs
    (data.grow 1) work h.dataCarry_canGrow_one h.work_canGrow_one h.dataCarry_work_disjoint

/-- Width of the comparator scratch register needed by Step 4. -/
def cmpLtNWWidth (N : ℕ) (data work : Reg) : ℕ :=
  2 + max (regSize data + regSize work) (Nat.log2 (N + 1) + 1 + regSize work)

/-- Static workspace condition for the Step-4 comparator. -/
structure CmpLtNWWorkspace (N : ℕ) (data work scratch : ExtReg) (flag : ℕ) where
  data_can_grow : data.CanGrow 1
  mulWorkspace : Gate.PhaseProdWorkspace work.active scratch.active
  mul_xReserve_eq : mulWorkspace.xReserve = work.reserve
  mul_zReserve_eq : mulWorkspace.zReserve = scratch.reserve
  data_work_disjoint : ExtReg.OwnedDisjoint data work
  data_scratch_disjoint : ExtReg.OwnedDisjoint data scratch
  work_scratch_disjoint : ExtReg.OwnedDisjoint work scratch
  flag_not_data : flag ∉ data.ownedQubits
  flag_not_work : flag ∉ work.ownedQubits
  flag_not_scratch : flag ∉ scratch.ownedQubits
  scratch_width : regSize scratch.active = cmpLtNWWidth N data.active work.active

/-- Static physical conditions needed by the concrete constant-arithmetic
lowerers.  Cleanliness is deliberately kept out of this record. -/
structure ConstArithmeticWorkspace (N : ℕ) (data scratch : ExtReg) (flag : ℕ) : Prop where
  data_can_grow : data.CanGrow 1
  scratch_can_grow : scratch.CanGrow 1
  data_scratch_disjoint : data.OwnedDisjoint scratch
  flag_not_data : flag ∉ data.ownedQubits
  flag_not_scratch : flag ∉ scratch.ownedQubits
  scratch_positive : 0 < scratch.width
  constant_fits : N < 2 ^ (scratch.width - 1)
  data_width_fits : data.width ≤ scratch.width - 1

end Shor
