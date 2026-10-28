import ForShor.ShorVerification.Framework.Semantics.GateSemantics
import ForShor.ShorVerification.Implementation.Shared.Registers
import ForShor.ShorVerification.Implementation.Shared.States
import ForShor.ShorVerification.Implementation.PhaseProduct.Compiler.Workspace
import ForShor.ShorVerification.Implementation.PhaseProduct.Compiler.PolicyWorkspace
import ForShor.ShorVerification.Implementation.PhaseProduct.Gates.Macros
import ForShor.ShorVerification.Implementation.PhaseProduct.Lowering.Plan
import ForShor.ShorVerification.Implementation.PhaseProduct.Lowering.PlanBuilders

/-!
# QFT: the lowering and its correctness statement

Everything needed to state the propositions proved in `Main.lean`. This file
imports nothing else from `QFT/`.
-/

namespace Shor

open Gate
open Operations
open scoped BigOperators

/-! =========================================================
    Workspace budget
========================================================= -/

/--
The QFT reserve recursion, abstracted over the phase-product reserve model it
calls at the middle phase product.

The abstraction is what lets the fixed-table and policy budgets share one
definition and one set of monotonicity lemmas: `qftWorkspaceNeed ops` and
`Policy.qftWorkspaceNeed P` are the two specialisations, and
`Policy.qftWorkspaceNeed_const` is the bridge between them.
-/
def qftWorkspaceNeedOf (res : ℕ → ℕ → ℕ × ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | 1 => (0, 0)
  | n + 2 =>
      let total := n + 2
      let leftWidth := total / 2
      let rightWidth := total - leftWidth
      let phaseNeed := res (leftWidth + 1) (rightWidth + 1)
      let leftNeed := qftWorkspaceNeedOf res leftWidth
      let rightNeed := qftWorkspaceNeedOf res rightWidth
      (max (1 + phaseNeed.1) (max leftNeed.1 rightNeed.1),
        max (1 + phaseNeed.2) (max leftNeed.2 rightNeed.2))
termination_by n => n

/-- The fixed-table QFT budget: unchanged in meaning and in spelling. -/
def qftWorkspaceNeed {k : ℕ} (ops : Prog k) : ℕ → ℕ × ℕ :=
  qftWorkspaceNeedOf (RecursivePhaseWorkspace.reserveNeed ops)

/-- The QFT budget under a policy: the same recursion over the policy's
reserve model. -/
def Policy.qftWorkspaceNeed (P : ShorLoweringPolicy) : ℕ → ℕ × ℕ :=
  qftWorkspaceNeedOf (Policy.reserveNeed P)

/-- Bridge: at the constant policy the QFT budget is the fixed table's. -/
theorem Policy.qftWorkspaceNeed_const (T : ToomCookTable) :
    Policy.qftWorkspaceNeed (ShorLoweringPolicy.constPolicy T)
      = _root_.Shor.qftWorkspaceNeed T.ops := by
  unfold Policy.qftWorkspaceNeed _root_.Shor.qftWorkspaceNeed
  congr 1
  funext wx wz
  exact Policy.reserveNeed_const T wx wz

/-! =========================================================
    Workspace registers and static preconditions
========================================================= -/

/--
The prefix of the inactive part of `r` assigned to the x-side workspace.
-/
def qftXWorkOf (need : ℕ → ℕ × ℕ) (r : ExtReg) : Reg :=
  r.reserve.take (need r.width).1

/-- The fixed-table spelling. -/
abbrev qftXWork {k : ℕ} (ops : Prog k) (r : ExtReg) : Reg :=
  qftXWorkOf (qftWorkspaceNeed ops) r

/-- The policy spelling. -/
abbrev Policy.qftXWork (P : ShorLoweringPolicy) (r : ExtReg) : Reg :=
  qftXWorkOf (Policy.qftWorkspaceNeed P) r

/--
The part of the inactive register following `qftXWork`, assigned to the
z-side workspace.
-/
def qftZWorkOf (need : ℕ → ℕ × ℕ) (r : ExtReg) : Reg :=
  let xNeed := (need r.width).1
  let zNeed := (need r.width).2
  (r.reserve.drop xNeed).take zNeed

/-- The fixed-table spelling. -/
abbrev qftZWork {k : ℕ} (ops : Prog k) (r : ExtReg) : Reg :=
  qftZWorkOf (qftWorkspaceNeed ops) r

/-- The policy spelling. -/
abbrev Policy.qftZWork (P : ShorLoweringPolicy) (r : ExtReg) : Reg :=
  qftZWorkOf (Policy.qftWorkspaceNeed P) r

/--
The inactive part of the QFT register is large enough to hold both concrete
workspace pools used by the recursive lowering.
-/
structure QFTReserveOKOf (need : ℕ → ℕ × ℕ) (r : ExtReg) : Prop where
  reserve_large_enough :
    (need r.width).1 + (need r.width).2 ≤ r.capacity

/-- The fixed-table spelling. -/
abbrev QFTReserveOK {k : ℕ} (ops : Prog k) (r : ExtReg) : Prop :=
  QFTReserveOKOf (qftWorkspaceNeed ops) r

/-- The policy spelling. -/
abbrev Policy.QFTReserveOK (P : ShorLoweringPolicy) (r : ExtReg) : Prop :=
  QFTReserveOKOf (Policy.qftWorkspaceNeed P) r

/--
Internal static condition for an already-selected pair of workspace
registers.  The public QFT lowering derives this condition from
`QFTReserveOK`.
-/
structure QFTWorkspaceOKOf (need : ℕ → ℕ × ℕ) (r xWork zWork : Reg) : Prop where
  data_x_disjoint : Disjoint r xWork
  data_z_disjoint : Disjoint r zWork
  work_disjoint : Disjoint xWork zWork
  x_large_enough : (need (regSize r)).1 ≤ regSize xWork
  z_large_enough : (need (regSize r)).2 ≤ regSize zWork

/-- The fixed-table spelling. Unchanged in meaning; every field name and every
`hworkspace.…` use site is unaffected. -/
abbrev QFTWorkspaceOK {k : ℕ} (ops : Prog k) (r xWork zWork : Reg) : Prop :=
  QFTWorkspaceOKOf (qftWorkspaceNeed ops) r xWork zWork

/-- The policy spelling. -/
abbrev Policy.QFTWorkspaceOK (P : ShorLoweringPolicy) (r xWork zWork : Reg) : Prop :=
  QFTWorkspaceOKOf (Policy.qftWorkspaceNeed P) r xWork zWork

/-- Bridge: at the constant policy the two coincide. -/
theorem Policy.qftWorkspaceOK_const_iff {T : ToomCookTable} {r xWork zWork : Reg} :
    Policy.QFTWorkspaceOK (ShorLoweringPolicy.constPolicy T) r xWork zWork
      ↔ _root_.Shor.QFTWorkspaceOK T.ops r xWork zWork := by
  unfold Policy.QFTWorkspaceOK _root_.Shor.QFTWorkspaceOK
  rw [Policy.qftWorkspaceNeed_const]

namespace QFTReserveOKOf

lemma explicitWorkspace {need : ℕ → ℕ × ℕ} {r : ExtReg}
    (hworkspace : QFTReserveOKOf need r) :
    QFTWorkspaceOKOf need r.active (qftXWorkOf need r) (qftZWorkOf need r) := by
  refine {
    data_x_disjoint := ?_
    data_z_disjoint := ?_
    work_disjoint := List.disjoint_of_subset_right (List.take_subset _ _)
      (List.disjoint_take_drop r.reserve.nodup le_rfl)
    x_large_enough := ?_
    z_large_enough := ?_
  }
  · exact List.disjoint_of_subset_right (fun q hq => List.mem_of_mem_take hq) r.active_reserve_disjoint
  · exact List.disjoint_of_subset_right (fun q hq => List.mem_of_mem_drop (List.mem_of_mem_take hq)) r.active_reserve_disjoint
  · have := hworkspace.reserve_large_enough
    simp [qftXWorkOf, Reg.take, regSize, Reg.width, ExtReg.capacity, ExtReg.width] at *; omega
  · have := hworkspace.reserve_large_enough
    simp [qftZWorkOf, Reg.take, Reg.drop, regSize, Reg.width, ExtReg.capacity, ExtReg.width] at *; omega

end QFTReserveOKOf

/-! =========================================================
    Child workspaces
========================================================= -/

lemma Gate.PhaseProdWorkspace.ownedDisjoint_grow {x z : Reg} (ws : Gate.PhaseProdWorkspace x z) :
    ExtReg.OwnedDisjoint (ws.xExt.grow 1) (ws.zExt.grow 1) := by
  unfold ExtReg.OwnedDisjoint
  rw [ExtReg.ownedQubits_grow, ExtReg.ownedQubits_grow]
  change (x.qubits ++ ws.xReserve.qubits).Disjoint (z.qubits ++ ws.zReserve.qubits)
  rw [List.disjoint_left]
  intro q hqx hqz
  rw [List.mem_append] at hqx hqz
  rcases hqx with hqx | hqxReserve
  · rcases hqz with hqz | hqzReserve
    · exact ws.xz_disjoint hqx hqz
    · exact ws.zReserve_not_x hqzReserve hqx
  · rcases hqz with hqz | hqzReserve
    · exact ws.xReserve_not_z hqxReserve hqz
    · exact ws.reserve_disjoint hqxReserve hqzReserve

namespace QFTWorkspaceOKOf

variable {res : ℕ → ℕ → ℕ × ℕ} {r xWork zWork : Reg}

/--
Construct the concrete unsigned phase-product workspace at the current QFT
node from the two root workspace registers.
-/
def phaseWorkspace (hworkspace : QFTWorkspaceOKOf (qftWorkspaceNeedOf res) r xWork zWork) (hsize : 2 ≤ regSize r) :
    Gate.PhaseProdWorkspace (leftReg r) (rightReg r) := by
  have hleftX : Disjoint (leftReg r) xWork := by
    exact List.disjoint_of_subset_left (fun q hq => List.mem_of_mem_take hq) hworkspace.data_x_disjoint
  have hleftZ : Disjoint (leftReg r) zWork := by
    exact List.disjoint_of_subset_left (fun q hq => List.mem_of_mem_take hq) hworkspace.data_z_disjoint
  have hrightX : Disjoint (rightReg r) xWork := by
    exact List.disjoint_of_subset_left (fun q hq => List.mem_of_mem_drop hq) hworkspace.data_x_disjoint
  have hrightZ : Disjoint (rightReg r) zWork := by
    exact List.disjoint_of_subset_left (fun q hq => List.mem_of_mem_drop hq) hworkspace.data_z_disjoint
  have hxNeed : 1 ≤ (qftWorkspaceNeedOf res (regSize r)).1 := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' hsize; simp [hm, qftWorkspaceNeedOf]
  have hzNeed : 1 ≤ (qftWorkspaceNeedOf res (regSize r)).2 := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' hsize; simp [hm, qftWorkspaceNeedOf]
  exact {
    xReserve := xWork
    zReserve := zWork
    x_can_grow := le_trans hxNeed hworkspace.x_large_enough
    z_can_grow := le_trans hzNeed hworkspace.z_large_enough
    xz_disjoint := splitLeft_splitRight_disjoint (r := r) (m := halfSplitPoint r)
    x_reserve_disjoint := hleftX
    z_reserve_disjoint := hrightZ
    xReserve_not_z := Disjoint.symm hrightX
    zReserve_not_x := Disjoint.symm hleftZ
    reserve_disjoint := hworkspace.work_disjoint
  }

/--
The root workspace condition remains valid for the left recursive QFT.
-/
lemma policySignedWorkspaceOK {P : ShorLoweringPolicy} {r xWork zWork : Reg}
    (hworkspace : Policy.QFTWorkspaceOK P r xWork zWork) (hsize : 2 ≤ regSize r) :
    let ws := hworkspace.phaseWorkspace hsize
    Policy.WorkspaceOK P (ws.xExt.grow 1) (ws.zExt.grow 1) := by
  dsimp only
  let ws := hworkspace.phaseWorkspace hsize
  have hxWidth : (ws.xExt.grow 1).width = regSize (leftReg r) + 1 := by
    calc
      (ws.xExt.grow 1).width = ws.xExt.width + 1 := ExtReg.width_grow ws.xExt 1 ws.xExt_canGrow
      _ = regSize (leftReg r) + 1 := rfl
  have hzWidth : (ws.zExt.grow 1).width = regSize (rightReg r) + 1 := by
    calc
      (ws.zExt.grow 1).width = ws.zExt.width + 1 := ExtReg.width_grow ws.zExt 1 ws.zExt_canGrow
      _ = regSize (rightReg r) + 1 := rfl
  have hxCapacity : (ws.xExt.grow 1).capacity = regSize xWork - 1 := by
    calc
      (ws.xExt.grow 1).capacity = ws.xExt.capacity - 1 :=
        ExtReg.capacity_grow ws.xExt 1 ws.xExt_canGrow
      _ = regSize xWork - 1 := rfl
  have hzCapacity : (ws.zExt.grow 1).capacity = regSize zWork - 1 := by
    calc
      (ws.zExt.grow 1).capacity = ws.zExt.capacity - 1 :=
        ExtReg.capacity_grow ws.zExt 1 ws.zExt_canGrow
      _ = regSize zWork - 1 := rfl
  have hxPhaseBound :
      1 + (Policy.reserveNeed P
        (regSize (leftReg r) + 1) (regSize (rightReg r) + 1)).1 ≤ regSize xWork := by
    rw [regSize_leftReg, regSize_rightReg]
    exact le_trans (by obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' hsize; simp [hm, Policy.qftWorkspaceNeed, qftWorkspaceNeedOf])
      hworkspace.x_large_enough
  have hzPhaseBound :
      1 + (Policy.reserveNeed P
        (regSize (leftReg r) + 1) (regSize (rightReg r) + 1)).2 ≤ regSize zWork := by
    rw [regSize_leftReg, regSize_rightReg]
    exact le_trans (by obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' hsize; simp [hm, Policy.qftWorkspaceNeed, qftWorkspaceNeedOf])
      hworkspace.z_large_enough
  refine {
    owned_disjoint := Gate.PhaseProdWorkspace.ownedDisjoint_grow ws
    x_reserve_sufficient := ?_
    z_reserve_sufficient := ?_
  }
  · rw [hxWidth, hzWidth, hxCapacity]
    omega
  · rw [hxWidth, hzWidth, hzCapacity]
    omega

/-- (Policy form.)
The root workspace condition remains valid for the left recursive QFT.
-/
lemma left (hworkspace : QFTWorkspaceOKOf (qftWorkspaceNeedOf res) r xWork zWork) (hsize : 2 ≤ regSize r) :
    QFTWorkspaceOKOf (qftWorkspaceNeedOf res) (leftReg r) xWork zWork := by
  refine {
    data_x_disjoint := ?_
    data_z_disjoint := ?_
    work_disjoint := hworkspace.work_disjoint
    x_large_enough := ?_
    z_large_enough := ?_
  }
  · exact List.disjoint_of_subset_left (fun q hq => List.mem_of_mem_take hq) hworkspace.data_x_disjoint
  · exact List.disjoint_of_subset_left (fun q hq => List.mem_of_mem_take hq) hworkspace.data_z_disjoint
  · simpa using le_trans (show (qftWorkspaceNeedOf res (regSize r / 2)).1 ≤ _ by
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' hsize; simp [hm, qftWorkspaceNeedOf])
      hworkspace.x_large_enough
  · simpa using le_trans (show (qftWorkspaceNeedOf res (regSize r / 2)).2 ≤ _ by
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' hsize; simp [hm, qftWorkspaceNeedOf])
      hworkspace.z_large_enough

/--
The root workspace condition remains valid for the right recursive QFT.
-/
lemma right (hworkspace : QFTWorkspaceOKOf (qftWorkspaceNeedOf res) r xWork zWork) (hsize : 2 ≤ regSize r) :
    QFTWorkspaceOKOf (qftWorkspaceNeedOf res) (rightReg r) xWork zWork := by
  refine {
    data_x_disjoint := ?_
    data_z_disjoint := ?_
    work_disjoint := hworkspace.work_disjoint
    x_large_enough := ?_
    z_large_enough := ?_
  }
  · exact List.disjoint_of_subset_left (fun q hq => List.mem_of_mem_drop hq) hworkspace.data_x_disjoint
  · exact List.disjoint_of_subset_left (fun q hq => List.mem_of_mem_drop hq) hworkspace.data_z_disjoint
  · simpa using le_trans (show (qftWorkspaceNeedOf res (regSize r - regSize r / 2)).1 ≤ _ by
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' hsize; simp [hm, qftWorkspaceNeedOf])
      hworkspace.x_large_enough
  · simpa using le_trans (show (qftWorkspaceNeedOf res (regSize r - regSize r / 2)).2 ≤ _ by
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' hsize; simp [hm, qftWorkspaceNeedOf])
      hworkspace.z_large_enough

end QFTWorkspaceOKOf

/-! =========================================================
    Lowering plans
========================================================= -/

/--
A complete physical lowering plan for one QFT.

The phase plan is intentionally explicit.  This is the point at which a caller
chooses either a base-case signed phase product or a recursive implementation
with concrete reserve layouts.
-/
inductive QFTLoweringPlan (P : ShorLoweringPolicy) : Reg → Type
  | empty (r : Reg) (hsize : regSize r = 0) : QFTLoweringPlan P r
  | singleton (r : Reg) (hsize : regSize r = 1) : QFTLoweringPlan P r
  | split
      (r : Reg) (hsize : 2 ≤ regSize r) (ws : Gate.PhaseProdWorkspace (leftReg r) (rightReg r))
      (phaseInitSize : ℕ)
      (phasePlan : PhaseLoweringPlan P phaseInitSize (Gate.PhaseProdUsing (qftPhi (regSize r)) (leftReg r) (rightReg r) ws))
      (rightPlan : QFTLoweringPlan P (rightReg r))
      (leftPlan : QFTLoweringPlan P (leftReg r)) :
      QFTLoweringPlan P r

/--
The fixed-table spelling of a QFT plan: the policy plan at the constant
policy, exactly as `StandardPhaseLoweringPlan` is for phase products. Every
existing caller keeps its five table arguments.
-/
abbrev StandardQFTLoweringPlan
    (k : ℕ) (hk : 1 < k) (pts : List Point) (hpts : pts.length = q k) (ops : Prog k)
    (r : Reg) : Type :=
  QFTLoweringPlan (ShorLoweringPolicy.constPolicy ⟨k, hk, pts, hpts, ops⟩) r

def lowerQFTPlan
    {P : ShorLoweringPolicy} {r : Reg}
    (plan : QFTLoweringPlan P r) :
    LowGate :=
  match plan with
  | .empty r hsize => LowGate.id
  | .singleton r hsize => LowGate.H (r.lowQubit (by omega))
  | .split r hsize ws phaseInitSize phasePlan rightPlan leftPlan =>
      lowerQFTPlan rightPlan ;;
      lowerGateRec phasePlan ;;
      lowerQFTPlan leftPlan ;;
      LowGate.RadixReverse r (regSize r / 2)

/-! =========================================================
    The unsigned phase-product subplan
========================================================= -/

/--
Construct the canonical lowering plan for an unsigned phase product.

The plan follows the definition of `Gate.PhaseProdUsing`:

1. zero-extend `x`;
2. zero-extend `z`;
3. recursively lower the resulting signed phase product;
4. deallocate the `z` extension;
5. deallocate the `x` extension.
-/
def Policy.phaseProdUsingPlan
    (P : ShorLoweringPolicy)
    (phi : Angle) {x z : Reg}
    (ws : Gate.PhaseProdWorkspace x z)
    (hworkspace : Policy.WorkspaceOK P (ws.xExt.grow 1) (ws.zExt.grow 1)) :
    PhaseLoweringPlan P (phaseInputSize (ws.xExt.grow 1) (ws.zExt.grow 1))
      (Gate.PhaseProdUsing phi x z ws) := by
  let initSize : ℕ := phaseInputSize (ws.xExt.grow 1) (ws.zExt.grow 1)
  let xExt : ExtReg := ws.xExt
  let zExt : ExtReg := ws.zExt
  let xSigned : ExtReg := xExt.grow 1
  let zSigned : ExtReg := zExt.grow 1

  let extendXPlan : PhaseLoweringPlan P initSize (Gate.zeroExtend xExt 1) :=
    PhaseLoweringPlan.zeroExtend initSize xExt 1

  let extendZPlan : PhaseLoweringPlan P initSize (Gate.zeroExtend zExt 1) :=
    PhaseLoweringPlan.zeroExtend initSize zExt 1

  let signedPlan :
      PhaseLoweringPlan P initSize (Gate.SignedPhaseProd phi xSigned zSigned) := by
    have hsize : phaseInputSize xSigned zSigned = initSize := by rfl
    simpa [hsize] using
      Policy.signedPlan P phi xSigned zSigned hworkspace

  let deallocZPlan : PhaseLoweringPlan P initSize (Gate.zeroDealloc zExt 1) :=
    PhaseLoweringPlan.zeroDealloc initSize zExt 1

  let deallocXPlan : PhaseLoweringPlan P initSize (Gate.zeroDealloc xExt 1) :=
    PhaseLoweringPlan.zeroDealloc initSize xExt 1

  let completePlan :
      PhaseLoweringPlan P initSize
        (Gate.zeroExtend xExt 1 ;;
          Gate.zeroExtend zExt 1 ;;
          Gate.SignedPhaseProd phi xSigned zSigned ;;
          Gate.zeroDealloc zExt 1 ;;
          Gate.zeroDealloc xExt 1) :=
    PhaseLoweringPlan.seq extendXPlan
      (PhaseLoweringPlan.seq extendZPlan
        (PhaseLoweringPlan.seq signedPlan
          (PhaseLoweringPlan.seq deallocZPlan deallocXPlan)))

  simpa [Gate.PhaseProdUsing, initSize, xExt, zExt, xSigned, zSigned]
    using completePlan

/-! =========================================================
    The canonical plan and the lowered QFT
========================================================= -/

/--
Build the standard recursive QFT plan from explicit x-side and z-side
workspace pools satisfying `QFTWorkspaceOK`.
-/
def Policy.qftPlan
    (P : ShorLoweringPolicy)
    (r xWork zWork : Reg)
    (hworkspace : Policy.QFTWorkspaceOK P r xWork zWork) :
    QFTLoweringPlan P r := by
  by_cases hzero : regSize r = 0
  · exact QFTLoweringPlan.empty r hzero
  · by_cases hone : regSize r = 1
    · exact QFTLoweringPlan.singleton r hone
    · have hlarge : 2 ≤ regSize r := by omega

      let ws : Gate.PhaseProdWorkspace (leftReg r) (rightReg r) :=
        hworkspace.phaseWorkspace hlarge

      have hphaseWorkspace :
          Policy.WorkspaceOK P (ws.xExt.grow 1) (ws.zExt.grow 1) := by
        simpa [ws] using hworkspace.policySignedWorkspaceOK hlarge

      have hrightWorkspace : Policy.QFTWorkspaceOK P (rightReg r) xWork zWork :=
        hworkspace.right hlarge

      have hleftWorkspace : Policy.QFTWorkspaceOK P (leftReg r) xWork zWork :=
        hworkspace.left hlarge

      let phasePlan : PhaseLoweringPlan P (phaseInputSize (ws.xExt.grow 1) (ws.zExt.grow 1))
          (Gate.PhaseProdUsing (qftPhi (regSize r)) (leftReg r) (rightReg r) ws) :=
        Policy.phaseProdUsingPlan P (qftPhi (regSize r)) ws hphaseWorkspace

      let rightPlan : QFTLoweringPlan P (rightReg r) :=
        Policy.qftPlan P (rightReg r) xWork zWork hrightWorkspace

      let leftPlan : QFTLoweringPlan P (leftReg r) :=
        Policy.qftPlan P (leftReg r) xWork zWork hleftWorkspace

      exact QFTLoweringPlan.split r hlarge ws (phaseInputSize (ws.xExt.grow 1) (ws.zExt.grow 1))
          phasePlan rightPlan leftPlan
termination_by regSize r
decreasing_by
  · have hhalfPos : 0 < regSize r / 2 := Nat.div_pos (by omega) (by decide)
    have hright : regSize r - regSize r / 2 < regSize r :=
      Nat.sub_lt (by omega) hhalfPos
    simpa [rightReg, halfSplitPoint] using hright
  · have hleft : regSize r / 2 < regSize r := Nat.div_lt_self (by omega) (by decide)
    simpa [leftReg, halfSplitPoint] using hleft

/-- The fixed-table spelling: the policy planner at the constant policy. -/
def standardQFTLoweringPlan
    (k : ℕ) (hk : 1 < k) (ops : Prog k) (pts : List Point) (hpts : pts.length = q k)
    (r xWork zWork : Reg)
    (hworkspace : QFTWorkspaceOK ops r xWork zWork) :
    StandardQFTLoweringPlan k hk pts hpts ops r :=
  Policy.qftPlan (ShorLoweringPolicy.constPolicy ⟨k, hk, pts, hpts, ops⟩) r xWork zWork
    (Policy.qftWorkspaceOK_const_iff.mpr hworkspace)

/--
Canonical reserve-backed QFT plan.

The canonical plan obtained by splitting the inactive portion of `r`. This is
the bridge from the public reserve predicate `QFTReserveOK` to the recursive
QFT plan used by the low-level lowerer.
-/
def Policy.reserveQftPlan
    (P : ShorLoweringPolicy)
    (r : ExtReg) (hworkspace : Policy.QFTReserveOK P r) :
    QFTLoweringPlan P r.active :=
  Policy.qftPlan P r.active (Policy.qftXWork P r) (Policy.qftZWork P r)
    hworkspace.explicitWorkspace

/-- The fixed-table spelling. Its workspace pools stay the `ops`-keyed
slices, so nothing downstream has to transport along the pool bridges. -/
def reserveQFTLoweringPlan
    (k : ℕ) (hk : 1 < k) (ops : Prog k) (pts : List Point) (hpts : pts.length = q k)
    (r : ExtReg) (hworkspace : QFTReserveOK ops r) :
    StandardQFTLoweringPlan k hk pts hpts ops r.active :=
  standardQFTLoweringPlan k hk ops pts hpts r.active (qftXWork ops r) (qftZWork ops r)
    hworkspace.explicitWorkspace

/--
The canonical lowered QFT. Its workspace is selected deterministically from
`r.reserve`; callers do not supply separate physical workspace registers.
-/
def Policy.lowerQFT
    (P : ShorLoweringPolicy)
    (r : ExtReg) (hworkspace : Policy.QFTReserveOK P r) :
    LowGate :=
  lowerQFTPlan (Policy.reserveQftPlan P r hworkspace)

/-- The fixed-table spelling. -/
def lowerQFT
    (k : ℕ) (hk : 1 < k) (ops : Prog k) (pts : List Point) (hpts : pts.length = q k)
    (r : ExtReg) (hworkspace : QFTReserveOK ops r) :
    LowGate :=
  lowerQFTPlan (reserveQFTLoweringPlan k hk ops pts hpts r hworkspace)

/-! =========================================================
    Workspace precondition on states
========================================================= -/

/--
The linear subspace in which both portions of the inactive QFT register used
by the concrete lowering are zero.
-/
abbrev QFTWorkspaceCleanState (qs : QSemantics) [RegEncoding qs.Basis] (xWork zWork : Reg) :
    qs.State → Prop :=
  CleanClosure (fun b => FreshZero xWork b ∧ FreshZero zWork b)

/--
The public precondition for concrete QFT lowering.  It says only that the
inactive part of the supplied `ExtReg` is large enough and that the two slices
selected by the lowering are initially zero.
-/
structure QFTWorkspaceStateOK
    (qs : QSemantics) [RegEncoding qs.Basis] {k : ℕ} (ops : Prog k) (r : ExtReg) (ψ : qs.State) :
    Prop where
  static : QFTReserveOK ops r
  clean : QFTWorkspaceCleanState qs (qftXWork ops r) (qftZWork ops r) ψ

/-- The policy spelling of the public QFT workspace precondition. -/
structure Policy.QFTWorkspaceStateOK
    (qs : QSemantics) [RegEncoding qs.Basis] (P : ShorLoweringPolicy) (r : ExtReg)
    (ψ : qs.State) : Prop where
  /-- The reserve is large enough for the whole policy-driven QFT recursion. -/
  static : Policy.QFTReserveOK P r
  /-- Both workspace pools are clean. -/
  clean : QFTWorkspaceCleanState qs (Policy.qftXWork P r) (Policy.qftZWork P r) ψ

/-! =========================================================
    Correctness
========================================================= -/

/--
The canonical recursive lowering of a QFT gate has the same semantics as the
high-level `Gate.QFT` gate on states with valid, clean recursive workspace.
-/
def LowerQFTCorrect
    (qs : QSemantics)
    [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
    (k : ℕ) (hk : 1 < k) (ops : Prog k) (r : ExtReg) : Prop :=
  ∀ (ψ : qs.State) (pts : List Point) (hpts : pts.length = q k)
    (hworkspace : QFTWorkspaceStateOK qs ops r ψ)
    (hInterp : GoodToomCookPoints k pts hpts)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (hRun : run? ops State.start_state = some State.start_state),
    ⟦lowerQFT k hk ops pts hpts r hworkspace.static⟧ₗ ψ = ⟦Gate.QFT r⟧ ψ

/--
The policy form: the canonical recursive lowering of a QFT gate under a
policy agrees with `Gate.QFT`, provided every table the policy can choose is
admissible.
-/
def Policy.LowerQFTCorrect
    (qs : QSemantics)
    [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]
    (P : ShorLoweringPolicy) (r : ExtReg) : Prop :=
  ∀ (ψ : qs.State) (hworkspace : Policy.QFTWorkspaceStateOK qs P r ψ),
    P.Admissible →
    ⟦Policy.lowerQFT P r hworkspace.static⟧ₗ ψ = ⟦Gate.QFT r⟧ ψ

end Shor
