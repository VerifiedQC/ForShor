import FastMultiplication.ShorVerification.Implementation.QFT.Split
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Workspace
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Gates.Macros

/-!
# QFT Workspace Budget Model

The recursive-workspace size model for QFT lowering (`qftWorkspaceNeed` and
its bounds), the public workspace precondition on a single `ExtReg`
(`QFTReserveOK`), the internal static condition on an already-selected pair
of workspace registers (`QFTWorkspaceOK`), and the construction of the two
child workspaces a recursive QFT split needs.
-/

namespace Shor

open Gate
open scoped BigOperators

/-! =========================================================
    Recursive workspace budget model

    The QFT lowerer uses two global reserve pools. `qftWorkspaceNeed` computes
    how large those pools must be for a register of a given width, accounting
    for the middle phase product and both recursive QFT calls.
========================================================= -/

def qftWorkspaceNeed {k : ℕ} (ops : Prog k) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | 1 => (0, 0)
  | n + 2 =>
      let total := n + 2
      let leftWidth := total / 2
      let rightWidth := total - leftWidth
      let phaseNeed := RecursivePhaseWorkspace.reserveNeed ops (leftWidth + 1) (rightWidth + 1)
      let leftNeed := qftWorkspaceNeed ops leftWidth
      let rightNeed := qftWorkspaceNeed ops rightWidth
      (max (1 + phaseNeed.1) (max leftNeed.1 rightNeed.1),
        max (1 + phaseNeed.2) (max leftNeed.2 rightNeed.2))
termination_by n => n

/-! =========================================================
    Public QFT workspace sizes and clean-state predicates

    The public QFT lowerer takes one `ExtReg`. Its inactive reserve is split
    deterministically into an x-side pool and a z-side pool. The predicates in
    this section are the static and dynamic contracts for those pools.
========================================================= -/

/--
The prefix of the inactive part of `r` assigned to the x-side workspace.
-/
def qftXWork {k : ℕ} (ops : Prog k) (r : ExtReg) : Reg :=
  r.reserve.take (qftWorkspaceNeed ops r.width).1

/--
The part of the inactive register following `qftXWork`, assigned to the
z-side workspace.
-/
def qftZWork {k : ℕ} (ops : Prog k) (r : ExtReg) : Reg :=
  let xNeed := (qftWorkspaceNeed ops r.width).1
  let zNeed := (qftWorkspaceNeed ops r.width).2
  (r.reserve.drop xNeed).take zNeed

/--
The inactive part of the QFT register is large enough to hold both concrete
workspace pools used by the recursive lowering.
-/
structure QFTReserveOK {k : ℕ} (ops : Prog k) (r : ExtReg) : Prop where
  reserve_large_enough :
    (qftWorkspaceNeed ops r.width).1 + (qftWorkspaceNeed ops r.width).2 ≤ r.capacity

/--
Internal static condition for an already-selected pair of workspace
registers.  The public QFT lowering derives this condition from
`QFTReserveOK`.
-/
structure QFTWorkspaceOK {k : ℕ} (ops : Prog k) (r xWork zWork : Reg) : Prop where
  data_x_disjoint : Disjoint r xWork
  data_z_disjoint : Disjoint r zWork
  work_disjoint : Disjoint xWork zWork
  x_large_enough : (qftWorkspaceNeed ops (regSize r)).1 ≤ regSize xWork
  z_large_enough : (qftWorkspaceNeed ops (regSize r)).2 ≤ regSize zWork

/-! =========================================================
    Helper lemmas for the selected workspace slices

    These lemmas prove that the selected workspace registers have the requested
    sizes, remain inside the inactive reserve, and are disjoint from the active
    data register and from each other.
========================================================= -/

@[simp] lemma regSize_leftReg (r : Reg) : regSize (leftReg r) = regSize r / 2 := by
  simp [leftReg, halfSplitPoint, splitM]

@[simp] lemma regSize_rightReg (r : Reg) :
    regSize (rightReg r) = regSize r - regSize r / 2 := by
  simp [rightReg, halfSplitPoint, splitM]

lemma disjoint_of_left_subset
    {small big other : Reg} (hsub : ∀ q : ℕ, q ∈ small.qubits → q ∈ big.qubits)
    (hdisjoint : Disjoint big other) : Disjoint small other := by
  rw [Disjoint, List.disjoint_left] at hdisjoint ⊢
  intro q hqSmall hqOther
  exact hdisjoint (hsub q hqSmall) hqOther

lemma disjoint_of_right_subset
    {small big other : Reg} (hsub : ∀ q : ℕ, q ∈ small.qubits → q ∈ big.qubits)
    (hdisjoint : Disjoint other big) : Disjoint other small := by
  apply Disjoint.symm
  apply disjoint_of_left_subset hsub
  exact Disjoint.symm hdisjoint

lemma qftXWork_mem_reserve
    {k : ℕ} (ops : Prog k) (r : ExtReg) {q : ℕ}
    (hq : q ∈ (qftXWork ops r).qubits) : q ∈ r.reserve.qubits := by
  apply List.mem_of_mem_take
  simpa [qftXWork, Reg.take] using hq

lemma qftZWork_mem_reserve
    {k : ℕ} (ops : Prog k) (r : ExtReg) {q : ℕ}
    (hq : q ∈ (qftZWork ops r).qubits) : q ∈ r.reserve.qubits := by
  have hqDrop : q ∈ r.reserve.qubits.drop (qftWorkspaceNeed ops r.width).1 := by
    apply List.mem_of_mem_take
    simpa [qftZWork, Reg.take, Reg.drop] using hq
  exact List.mem_of_mem_drop hqDrop

lemma qftXWork_qftZWork_disjoint {k : ℕ} (ops : Prog k) (r : ExtReg) :
    Disjoint (qftXWork ops r) (qftZWork ops r) := by
  rw [Disjoint, List.disjoint_left]
  intro q hqx hqz
  have hqxTake : q ∈ r.reserve.qubits.take (qftWorkspaceNeed ops r.width).1 := by
    simpa [qftXWork, Reg.take] using hqx
  have hqzDrop : q ∈ r.reserve.qubits.drop (qftWorkspaceNeed ops r.width).1 := by
    apply List.mem_of_mem_take
    simpa [qftZWork, Reg.take, Reg.drop] using hqz
  have hdisjoint :=
    List.disjoint_take_drop r.reserve.nodup (le_refl (qftWorkspaceNeed ops r.width).1)
  rw [List.disjoint_left] at hdisjoint
  exact hdisjoint hqxTake hqzDrop

@[simp] lemma regSize_qftXWork
    {k : ℕ} (ops : Prog k) (r : ExtReg) (hworkspace : QFTReserveOK ops r) :
    regSize (qftXWork ops r) = (qftWorkspaceNeed ops r.width).1 := by
  have hxFits : (qftWorkspaceNeed ops r.width).1 ≤ r.capacity := by
    have htotal := hworkspace.reserve_large_enough
    omega
  simpa [qftXWork, Reg.take, regSize, Reg.width, ExtReg.capacity, Nat.min_eq_left hxFits]

@[simp] lemma regSize_qftZWork
    {k : ℕ} (ops : Prog k) (r : ExtReg) (hworkspace : QFTReserveOK ops r) :
    regSize (qftZWork ops r) = (qftWorkspaceNeed ops r.width).2 := by
  have hzFits :
      (qftWorkspaceNeed ops r.width).2 ≤ r.capacity - (qftWorkspaceNeed ops r.width).1 := by
    have htotal := hworkspace.reserve_large_enough
    omega
  simpa [
    qftZWork, Reg.take, Reg.drop, regSize, Reg.width, ExtReg.capacity, Nat.min_eq_left hzFits
  ]

namespace QFTReserveOK

lemma explicitWorkspace {k : ℕ} {ops : Prog k} {r : ExtReg}
    (hworkspace : QFTReserveOK ops r) :
    QFTWorkspaceOK ops r.active (qftXWork ops r) (qftZWork ops r) := by
  refine {
    data_x_disjoint := ?_
    data_z_disjoint := ?_
    work_disjoint := qftXWork_qftZWork_disjoint ops r
    x_large_enough := ?_
    z_large_enough := ?_
  }
  · apply disjoint_of_right_subset (fun q hq => qftXWork_mem_reserve ops r hq)
    exact r.active_reserve_disjoint
  · apply disjoint_of_right_subset (fun q hq => qftZWork_mem_reserve ops r hq)
    exact r.active_reserve_disjoint
  · rw [regSize_qftXWork ops r hworkspace]
    simp [ExtReg.width]
  · rw [regSize_qftZWork ops r hworkspace]
    simp [ExtReg.width]

end QFTReserveOK

/-! =========================================================
    Unfolding and bounds for `qftWorkspaceNeed`

    A nontrivial QFT split must reserve enough space for the middle phase
    product and both recursive QFT calls. These monotonicity lemmas let the
    plan constructor reuse the same workspace pools for each child.
========================================================= -/

lemma qftWorkspaceNeed_eq_of_two_le {k : ℕ} (ops : Prog k) (n : ℕ) (hn : 2 ≤ n) :
    qftWorkspaceNeed ops n =
      let leftWidth := n / 2
      let rightWidth := n - leftWidth
      let phaseNeed := RecursivePhaseWorkspace.reserveNeed ops (leftWidth + 1) (rightWidth + 1)
      let leftNeed := qftWorkspaceNeed ops leftWidth
      let rightNeed := qftWorkspaceNeed ops rightWidth
      (max (1 + phaseNeed.1) (max leftNeed.1 rightNeed.1),
        max (1 + phaseNeed.2) (max leftNeed.2 rightNeed.2)) := by
  cases n with
  | zero => omega
  | succ n =>
      cases n with
      | zero => omega
      | succ n => conv_lhs => unfold qftWorkspaceNeed

lemma qftWorkspaceNeed_phase_x_le {k : ℕ} (ops : Prog k) (n : ℕ) (hn : 2 ≤ n) :
    1 + (RecursivePhaseWorkspace.reserveNeed ops (n / 2 + 1) (n - n / 2 + 1)).1
      ≤ (qftWorkspaceNeed ops n).1 := by
  rw [qftWorkspaceNeed_eq_of_two_le ops n hn]
  dsimp only
  exact Nat.le_max_left _ _

lemma qftWorkspaceNeed_phase_z_le {k : ℕ} (ops : Prog k) (n : ℕ) (hn : 2 ≤ n) :
    1 + (RecursivePhaseWorkspace.reserveNeed ops (n / 2 + 1) (n - n / 2 + 1)).2
      ≤ (qftWorkspaceNeed ops n).2 := by
  rw [qftWorkspaceNeed_eq_of_two_le ops n hn]
  dsimp only
  exact Nat.le_max_left _ _

lemma qftWorkspaceNeed_left_x_le {k : ℕ} (ops : Prog k) (n : ℕ) (hn : 2 ≤ n) :
    (qftWorkspaceNeed ops (n / 2)).1 ≤ (qftWorkspaceNeed ops n).1 := by
  rw [qftWorkspaceNeed_eq_of_two_le ops n hn]
  dsimp only
  exact le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

lemma qftWorkspaceNeed_left_z_le {k : ℕ} (ops : Prog k) (n : ℕ) (hn : 2 ≤ n) :
    (qftWorkspaceNeed ops (n / 2)).2 ≤ (qftWorkspaceNeed ops n).2 := by
  rw [qftWorkspaceNeed_eq_of_two_le ops n hn]
  dsimp only
  exact le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

lemma qftWorkspaceNeed_right_x_le {k : ℕ} (ops : Prog k) (n : ℕ) (hn : 2 ≤ n) :
    (qftWorkspaceNeed ops (n - n / 2)).1 ≤ (qftWorkspaceNeed ops n).1 := by
  rw [qftWorkspaceNeed_eq_of_two_le ops n hn]
  dsimp only
  exact le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

lemma qftWorkspaceNeed_right_z_le {k : ℕ} (ops : Prog k) (n : ℕ) (hn : 2 ≤ n) :
    (qftWorkspaceNeed ops (n - n / 2)).2 ≤ (qftWorkspaceNeed ops n).2 := by
  rw [qftWorkspaceNeed_eq_of_two_le ops n hn]
  dsimp only
  exact le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

/-! =========================================================
    Building child workspaces and recursive QFT plans

    The functions and lemmas below carve the two workspace pools into the
    pieces needed by the middle phase product and by the left/right recursive
    QFT calls. They culminate in the canonical plan and public lowered circuit.
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

namespace QFTWorkspaceOK

variable {k : ℕ} {ops : Prog k} {r xWork zWork : Reg}

/--
Construct the concrete unsigned phase-product workspace at the current QFT
node from the two root workspace registers.
-/
def phaseWorkspace (hworkspace : QFTWorkspaceOK ops r xWork zWork) (hsize : 2 ≤ regSize r) :
    Gate.PhaseProdWorkspace (leftReg r) (rightReg r) := by
  have hleftX : Disjoint (leftReg r) xWork := by
    apply disjoint_of_left_subset (fun q hq => leftReg_mem_parent r hq)
    exact hworkspace.data_x_disjoint
  have hleftZ : Disjoint (leftReg r) zWork := by
    apply disjoint_of_left_subset (fun q hq => leftReg_mem_parent r hq)
    exact hworkspace.data_z_disjoint
  have hrightX : Disjoint (rightReg r) xWork := by
    apply disjoint_of_left_subset (fun q hq => rightReg_mem_parent r hq)
    exact hworkspace.data_x_disjoint
  have hrightZ : Disjoint (rightReg r) zWork := by
    apply disjoint_of_left_subset (fun q hq => rightReg_mem_parent r hq)
    exact hworkspace.data_z_disjoint
  have hxNeed : 1 ≤ (qftWorkspaceNeed ops (regSize r)).1 := by
    have hphase := qftWorkspaceNeed_phase_x_le ops (regSize r) hsize
    omega
  have hzNeed : 1 ≤ (qftWorkspaceNeed ops (regSize r)).2 := by
    have hphase := qftWorkspaceNeed_phase_z_le ops (regSize r) hsize
    omega
  exact {
    xReserve := xWork
    zReserve := zWork
    x_can_grow := le_trans hxNeed hworkspace.x_large_enough
    z_can_grow := le_trans hzNeed hworkspace.z_large_enough
    xz_disjoint := disjoint_left_right r
    x_reserve_disjoint := hleftX
    z_reserve_disjoint := hrightZ
    xReserve_not_z := Disjoint.symm hrightX
    zReserve_not_x := Disjoint.symm hleftZ
    reserve_disjoint := hworkspace.work_disjoint
  }

/--
The root workspace bound implies sufficient signed-phase-product workspace at
the current QFT node.
-/
lemma signedWorkspaceOK (hworkspace : QFTWorkspaceOK ops r xWork zWork) (hsize : 2 ≤ regSize r) :
    let ws := hworkspace.phaseWorkspace hsize
    SignedRecursiveWorkspaceOK ops (ws.xExt.grow 1) (ws.zExt.grow 1) := by
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
      1 + (RecursivePhaseWorkspace.reserveNeed ops
        (regSize (leftReg r) + 1) (regSize (rightReg r) + 1)).1 ≤ regSize xWork := by
    rw [regSize_leftReg, regSize_rightReg]
    exact le_trans (qftWorkspaceNeed_phase_x_le ops (regSize r) hsize) hworkspace.x_large_enough
  have hzPhaseBound :
      1 + (RecursivePhaseWorkspace.reserveNeed ops
        (regSize (leftReg r) + 1) (regSize (rightReg r) + 1)).2 ≤ regSize zWork := by
    rw [regSize_leftReg, regSize_rightReg]
    exact le_trans (qftWorkspaceNeed_phase_z_le ops (regSize r) hsize) hworkspace.z_large_enough
  refine {
    owned_disjoint := Gate.PhaseProdWorkspace.ownedDisjoint_grow ws
    x_reserve_sufficient := ?_
    z_reserve_sufficient := ?_
  }
  · rw [hxWidth, hzWidth, hxCapacity]
    omega
  · rw [hxWidth, hzWidth, hzCapacity]
    omega

/--
The root workspace condition remains valid for the left recursive QFT.
-/
lemma left (hworkspace : QFTWorkspaceOK ops r xWork zWork) (hsize : 2 ≤ regSize r) :
    QFTWorkspaceOK ops (leftReg r) xWork zWork := by
  refine {
    data_x_disjoint := ?_
    data_z_disjoint := ?_
    work_disjoint := hworkspace.work_disjoint
    x_large_enough := ?_
    z_large_enough := ?_
  }
  · apply disjoint_of_left_subset (fun q hq => leftReg_mem_parent r hq)
    exact hworkspace.data_x_disjoint
  · apply disjoint_of_left_subset (fun q hq => leftReg_mem_parent r hq)
    exact hworkspace.data_z_disjoint
  · simpa using le_trans (qftWorkspaceNeed_left_x_le ops (regSize r) hsize)
      hworkspace.x_large_enough
  · simpa using le_trans (qftWorkspaceNeed_left_z_le ops (regSize r) hsize)
      hworkspace.z_large_enough

/--
The root workspace condition remains valid for the right recursive QFT.
-/
lemma right (hworkspace : QFTWorkspaceOK ops r xWork zWork) (hsize : 2 ≤ regSize r) :
    QFTWorkspaceOK ops (rightReg r) xWork zWork := by
  refine {
    data_x_disjoint := ?_
    data_z_disjoint := ?_
    work_disjoint := hworkspace.work_disjoint
    x_large_enough := ?_
    z_large_enough := ?_
  }
  · apply disjoint_of_left_subset (fun q hq => rightReg_mem_parent r hq)
    exact hworkspace.data_x_disjoint
  · apply disjoint_of_left_subset (fun q hq => rightReg_mem_parent r hq)
    exact hworkspace.data_z_disjoint
  · simpa using le_trans (qftWorkspaceNeed_right_x_le ops (regSize r) hsize)
      hworkspace.x_large_enough
  · simpa using le_trans (qftWorkspaceNeed_right_z_le ops (regSize r) hsize)
      hworkspace.z_large_enough

end QFTWorkspaceOK

end Shor
