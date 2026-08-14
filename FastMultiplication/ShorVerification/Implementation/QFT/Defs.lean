import FastMultiplication.ShorVerification.Framework.Semantics.GateSemantics
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Defs
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.GateLevelCorrectness.GateSemanticsLemmas
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.LoweringCorrectness.Linearity

/-!
# QFT Public Definitions

Just enough definitions to state the QFT lowering-correctness assertion
(`Assertions.lean`). All proof-only material stays under `QFT.Proofs`.
-/
namespace Shor

open Gate

universe u




/-! =========================================================
    Section 1: Register arithmetic and split helpers
========================================================= -/

variable (qs : QSemantics)
  [RegEncoding qs.Basis]

  [GateSemanticsFacts qs]

def splitM (r : Reg) : ℕ := (regSize r) / 2
def halfSplitPoint (r : Reg) : SplitPoint r :=
  ⟨splitM r, by
    simpa [splitM] using Nat.div_le_self (regSize r) 2⟩

def leftReg  (r : Reg) : Reg := splitLeft r (halfSplitPoint r)
def rightReg (r : Reg) : Reg := splitRight r (halfSplitPoint r)

lemma leftReg_mem_parent
    (r : Reg)
    {q : ℕ}
    (hq : q ∈ (leftReg r).qubits) :
    q ∈ r.qubits := by
  simpa [
    leftReg,
    halfSplitPoint,
    splitM,
    splitLeft,
    Reg.take
  ] using List.mem_of_mem_take hq

lemma rightReg_mem_parent
    (r : Reg)
    {q : ℕ}
    (hq : q ∈ (rightReg r).qubits) :
    q ∈ r.qubits := by
  simpa [
    rightReg,
    halfSplitPoint,
    splitM,
    splitRight,
    Reg.drop
  ] using List.mem_of_mem_drop hq

namespace Gate.PhaseProdWorkspace

/--
The linear subspace in which both physical workspace qubits of an unsigned
phase-product macro are clean.
-/
abbrev CleanState
    (qs : QSemantics) [RegEncoding qs.Basis] {x z : Reg} (ws : Gate.PhaseProdWorkspace x z) : qs.State → Prop :=
  CleanClosure (fun b => ws.Clean b)

end Gate.PhaseProdWorkspace

lemma disjoint_left_right (r : Reg) :
  Disjoint (leftReg r) (rightReg r) := by
  simpa [leftReg, rightReg] using
    (splitLeft_splitRight_disjoint (r := r) (m := halfSplitPoint r))


/-! =========================================================
    Section 2: Encoding-only split-register lemmas
========================================================= -/

section EncodingOnly
variable (qs : QSemantics) [RegEncoding qs.Basis]

end EncodingOnly

/-! =========================================================
    Section 3: Exponential and qftPhase bridge lemmas
========================================================= -/

/-! =========================================================
    Section 4: Sum-pushing and scalar helper lemmas
========================================================= -/

/-! =========================================================
    Section 5: First split-QFT steps
========================================================= -/

/-! =========================================================
    Section 6: Phase-combination lemmas
========================================================= -/

/-! =========================================================
    Section 7: Reindexing sums and cast utilities
========================================================= -/

open scoped BigOperators


/-! =========================================================
    Section 8: QFT split on basis kets
========================================================= -/

/-! =========================================================
    Section 9: Radix reversal and exact QFT split
========================================================= -/





open Gate


/-! =========================================================
    Section 1: Explicit QFT lowering plans
========================================================= -/

/--
A complete physical lowering plan for one QFT.

The phase plan is intentionally explicit.  This is the point at which a caller
chooses either a base-case signed phase product or a recursive implementation
with concrete reserve layouts.
-/
inductive QFTLoweringPlan
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k) :
    Reg → Type

  | empty
      (r : Reg)
      (hsize : regSize r = 0) :
      QFTLoweringPlan k hk ops r

  | singleton
      (r : Reg)
      (hsize : regSize r = 1) :
      QFTLoweringPlan k hk ops r

  | split
      (r : Reg)
      (hsize : 2 ≤ regSize r)
      (ws : Gate.PhaseProdWorkspace (leftReg r) (rightReg r))
      (phaseInitSize : ℕ)
      (phasePlan :
        StandardPhaseLoweringPlan k hk ops
          phaseInitSize (Gate.PhaseProdUsing (qftPhi (regSize r)) (leftReg r) (rightReg r) ws))
      (rightPlan : QFTLoweringPlan k hk ops (rightReg r))
      (leftPlan : QFTLoweringPlan k hk ops (leftReg r)) :
      QFTLoweringPlan k hk ops r

noncomputable def lowerQFTPlan
    {k : ℕ}
    {hk : 1 < k}
    {ops : Prog k}
    {r : Reg}
    (plan : QFTLoweringPlan k hk ops r) :
    LowGate := by
  induction plan with
  | empty r hsize =>
      exact LowGate.id

  | singleton r hsize =>
      exact
        LowGate.H
          (r.lowQubit (by omega))

  | split r hsize ws phaseInitSize phasePlan
      rightPlan leftPlan lowerRight lowerLeft =>
      exact
        lowerRight ;;
        lowerGateRec phasePlan ;;
        lowerLeft ;;
        LowGate.RadixReverse r (splitM r)

noncomputable def QFTLoweringReady
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [LowerGateClass qs]
    {k : ℕ}
    {hk : 1 < k}
    {ops : Prog k}
    {r : Reg}
    (plan : QFTLoweringPlan k hk ops r) :
    qs.State → Prop := by
  induction plan with
  | empty r hsize =>
      exact fun _ => True

  | singleton r hsize =>
      exact fun _ => True

  | split r hsize ws phaseInitSize phasePlan
      rightPlan leftPlan readyRight readyLeft =>
      exact fun ψ =>
        Gate.PhaseProdWorkspace.CleanState qs ws ψ
        ∧
        readyRight ψ
        ∧
        let ψRight := LowerGateClass.evalL (qs := qs) (lowerQFTPlan rightPlan) ψ
        PhaseLoweringReady qs phasePlan ψRight
        ∧
        let ψPhase :=
          LowerGateClass.evalL (qs := qs) (lowerGateRec phasePlan) ψRight
        readyLeft ψPhase

/-! =========================================================
    Section 4: Linearity and workspace preservation
========================================================= -/

lemma evalL_lowerQFTPlan_zero
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    {k : ℕ}
    {hk : 1 < k}
    {ops : Prog k}
    {r : Reg}
    (plan : QFTLoweringPlan k hk ops r) :
    LowerGateClass.evalL
        (qs := qs)
        (lowerQFTPlan plan)
        0
      =
    0 := by
  exact LowerGateClass.evalL_zero (qs := qs) (lowerQFTPlan plan)


lemma QFTLoweringReady.zero
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [LowerGateClass qs]
    {k : ℕ}
    {hk : 1 < k}
    {ops : Prog k}
    {r : Reg}
    (plan : QFTLoweringPlan k hk ops r) :
    QFTLoweringReady qs plan 0 := by
  induction plan with
  | empty =>
      trivial
  | singleton =>
      trivial
  | split r hsize ws phaseInitSize phasePlan
      rightPlan leftPlan ihRight ihLeft =>
      change
        Gate.PhaseProdWorkspace.CleanState qs ws 0
          ∧
        QFTLoweringReady qs rightPlan 0
          ∧
        PhaseLoweringReady
          qs phasePlan
          (LowerGateClass.evalL
            (qs := qs)
            (lowerQFTPlan rightPlan)
            0)
          ∧
        QFTLoweringReady
          qs leftPlan
          (LowerGateClass.evalL
            (qs := qs)
            (lowerGateRec phasePlan)
            (LowerGateClass.evalL
              (qs := qs)
              (lowerQFTPlan rightPlan)
              0))
      rw [
        evalL_lowerQFTPlan_zero,
        evalL_lowerGateRec_zero
      ]
      exact
        ⟨
          CleanClosure.zero,
          ihRight,
          PhaseLoweringReady.zero qs phasePlan,
          ihLeft
        ⟩






open Gate


/-! =========================================================
    Section 1: Canonical unsigned phase-product plans

    A split QFT uses an unsigned phase product between the left and right
    halves. This section packages that unsigned gate as a standard
    phase-product lowering plan by zero-extending both operands, lowering the
    resulting signed phase product, and deallocating the extensions.
========================================================= -/

/--
The recursive signed-phase-product input size used by
`Gate.PhaseProdUsing`.
-/
def phaseProdUsingInputSize
    {x z : Reg}
    (ws : Gate.PhaseProdWorkspace x z) :
    ℕ :=
  phaseInputSize
    (ws.xExt.grow 1)
    (ws.zExt.grow 1)

/--
Construct the canonical lowering plan for an unsigned phase product.

The plan follows the definition of `Gate.PhaseProdUsing`:

1. zero-extend `x`;
2. zero-extend `z`;
3. recursively lower the resulting signed phase product;
4. deallocate the `z` extension;
5. deallocate the `x` extension.
-/
noncomputable def standardPhaseProdUsingPlan
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (phi : ℝ)
    {x z : Reg}
    (ws : Gate.PhaseProdWorkspace x z)
    (hworkspace :
      SignedRecursiveWorkspaceOK
        ops
        (ws.xExt.grow 1)
        (ws.zExt.grow 1)) :
    StandardPhaseLoweringPlan
      k
      hk
      ops
      (phaseProdUsingInputSize ws)
      (Gate.PhaseProdUsing phi x z ws) := by

  let initSize : ℕ :=
    phaseProdUsingInputSize ws

  let xExt : ExtReg :=
    ws.xExt

  let zExt : ExtReg :=
    ws.zExt

  let xSigned : ExtReg :=
    xExt.grow 1

  let zSigned : ExtReg :=
    zExt.grow 1

  let extendXPlan :
      StandardPhaseLoweringPlan
        k hk ops
        initSize
        (Gate.zeroExtend xExt 1) :=
    PhaseLoweringPlan.zeroExtend
      initSize
      xExt
      1

  let extendZPlan :
      StandardPhaseLoweringPlan
        k hk ops
        initSize
        (Gate.zeroExtend zExt 1) :=
    PhaseLoweringPlan.zeroExtend
      initSize
      zExt
      1

  let signedPlan :
      StandardPhaseLoweringPlan
        k hk ops
        initSize
        (Gate.SignedPhaseProd
          phi
          xSigned
          zSigned) := by
    have hsize :
        phaseInputSize xSigned zSigned =
          initSize := by
      rfl

    simpa [hsize] using
      standardSignedPhaseLoweringPlan
        k
        hk
        phi
        xSigned
        zSigned
        ops
        hworkspace

  let deallocZPlan :
      StandardPhaseLoweringPlan
        k hk ops
        initSize
        (Gate.zeroDealloc zExt 1) :=
    PhaseLoweringPlan.zeroDealloc
      initSize
      zExt
      1

  let deallocXPlan :
      StandardPhaseLoweringPlan
        k hk ops
        initSize
        (Gate.zeroDealloc xExt 1) :=
    PhaseLoweringPlan.zeroDealloc
      initSize
      xExt
      1

  let completePlan :
      StandardPhaseLoweringPlan
        k hk ops
        initSize
        (
          Gate.zeroExtend xExt 1 ;;
          Gate.zeroExtend zExt 1 ;;
          Gate.SignedPhaseProd
            phi
            xSigned
            zSigned ;;
          Gate.zeroDealloc zExt 1 ;;
          Gate.zeroDealloc xExt 1
        ) :=
    PhaseLoweringPlan.seq
      extendXPlan
      (PhaseLoweringPlan.seq
        extendZPlan
        (PhaseLoweringPlan.seq
          signedPlan
          (PhaseLoweringPlan.seq
            deallocZPlan
            deallocXPlan)))

  simpa [
    Gate.PhaseProdUsing,
    phaseProdUsingInputSize,
    initSize,
    xExt,
    zExt,
    xSigned,
    zSigned
  ] using completePlan


def qftWorkspaceNeed
    {k : ℕ}
    (ops : Prog k) :
    ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | 1 => (0, 0)
  | n + 2 =>
      let total := n + 2
      let leftWidth := total / 2
      let rightWidth := total - leftWidth

      let phaseNeed :=
        RecursivePhaseWorkspace.reserveNeed
          ops
          (leftWidth + 1)
          (rightWidth + 1)

      let leftNeed :=
        qftWorkspaceNeed ops leftWidth

      let rightNeed :=
        qftWorkspaceNeed ops rightWidth

      (
        max
          (1 + phaseNeed.1)
          (max leftNeed.1 rightNeed.1),

        max
          (1 + phaseNeed.2)
          (max leftNeed.2 rightNeed.2)
      )
termination_by n => n

/-! =========================================================
    Section 2: Public QFT workspace sizes and clean-state predicates

    The public QFT lowerer takes one `ExtReg`. Its inactive reserve is split
    deterministically into an x-side pool and a z-side pool. The predicates in
    this section are the static and dynamic contracts for those pools.
========================================================= -/

/--
The prefix of the inactive part of `r` assigned to the x-side workspace.
-/
def qftXWork
    {k : ℕ}
    (ops : Prog k)
    (r : ExtReg) :
    Reg :=
  r.reserve.take
    (qftWorkspaceNeed ops r.width).1

/--
The part of the inactive register following `qftXWork`, assigned to the
z-side workspace.
-/
def qftZWork
    {k : ℕ}
    (ops : Prog k)
    (r : ExtReg) :
    Reg :=
  let xNeed :=
    (qftWorkspaceNeed ops r.width).1
  let zNeed :=
    (qftWorkspaceNeed ops r.width).2
  (r.reserve.drop xNeed).take zNeed

/--
The inactive part of the QFT register is large enough to hold both concrete
workspace pools used by the recursive lowering.
-/
structure QFTReserveOK
    {k : ℕ}
    (ops : Prog k)
    (r : ExtReg) :
    Prop where

  reserve_large_enough :
    (qftWorkspaceNeed ops r.width).1
      +
    (qftWorkspaceNeed ops r.width).2
      ≤
    r.capacity

/--
The linear subspace in which both portions of the inactive QFT register used
by the concrete lowering are zero.
-/
abbrev QFTWorkspaceCleanState
    (qs : QSemantics) [RegEncoding qs.Basis] (xWork zWork : Reg) :
    qs.State → Prop :=
  CleanClosure (fun b => FreshZero xWork b ∧ FreshZero zWork b)

namespace QFTWorkspaceCleanState
variable {qs : QSemantics} [RegEncoding qs.Basis] {xWork zWork : Reg}
/-- Smart constructors delegating to `CleanClosure`, preserving call sites. -/
theorem zero : QFTWorkspaceCleanState qs xWork zWork 0 := CleanClosure.zero
end QFTWorkspaceCleanState

/--
The public precondition for concrete QFT lowering.  It says only that the
inactive part of the supplied `ExtReg` is large enough and that the two slices
selected by the lowering are initially zero.
-/
structure QFTWorkspaceStateOK
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    {k : ℕ}
    (ops : Prog k)
    (r : ExtReg)
    (ψ : qs.State) :
    Prop where

  static : QFTReserveOK ops r

  clean :
    QFTWorkspaceCleanState qs (qftXWork ops r) (qftZWork ops r) ψ

/--
Internal static condition for an already-selected pair of workspace
registers.  The public QFT lowering derives this condition from
`QFTReserveOK`.
-/
structure QFTWorkspaceOK
    {k : ℕ}
    (ops : Prog k)
    (r xWork zWork : Reg) :
    Prop where

  data_x_disjoint :
    Disjoint r xWork

  data_z_disjoint :
    Disjoint r zWork

  work_disjoint :
    Disjoint xWork zWork

  x_large_enough :
    (qftWorkspaceNeed ops (regSize r)).1 ≤
      regSize xWork

  z_large_enough :
    (qftWorkspaceNeed ops (regSize r)).2 ≤
      regSize zWork

/-! =========================================================
    Section 3: Helper lemmas for the selected workspace slices

    These lemmas prove that the selected workspace registers have the requested
    sizes, remain inside the inactive reserve, and are disjoint from the active
    data register and from each other.
========================================================= -/

@[simp] lemma regSize_leftReg
    (r : Reg) :
    regSize (leftReg r) =
      regSize r / 2 := by
  simp [
    leftReg,
    halfSplitPoint,
    splitM
  ]


@[simp] lemma regSize_rightReg
    (r : Reg) :
    regSize (rightReg r) =
      regSize r - regSize r / 2 := by
  simp [
    rightReg,
    halfSplitPoint,
    splitM
  ]


lemma disjoint_of_left_subset
    {small big other : Reg}
    (hsub :
      ∀ q : ℕ,
        q ∈ small.qubits →
        q ∈ big.qubits)
    (hdisjoint : Disjoint big other) :
    Disjoint small other := by
  rw [Disjoint, List.disjoint_left] at hdisjoint ⊢
  intro q hqSmall hqOther
  exact hdisjoint (hsub q hqSmall) hqOther


lemma disjoint_of_right_subset
    {small big other : Reg}
    (hsub :
      ∀ q : ℕ,
        q ∈ small.qubits →
        q ∈ big.qubits)
    (hdisjoint : Disjoint other big) :
    Disjoint other small := by
  apply Disjoint.symm
  apply disjoint_of_left_subset hsub
  exact Disjoint.symm hdisjoint

lemma qftXWork_mem_reserve
    {k : ℕ}
    (ops : Prog k)
    (r : ExtReg)
    {q : ℕ}
    (hq : q ∈ (qftXWork ops r).qubits) :
    q ∈ r.reserve.qubits := by
  apply List.mem_of_mem_take
  simpa [
    qftXWork,
    Reg.take
  ] using hq


lemma qftZWork_mem_reserve
    {k : ℕ}
    (ops : Prog k)
    (r : ExtReg)
    {q : ℕ}
    (hq : q ∈ (qftZWork ops r).qubits) :
    q ∈ r.reserve.qubits := by
  have hqDrop :
      q ∈
        r.reserve.qubits.drop
          (qftWorkspaceNeed ops r.width).1 := by
    apply List.mem_of_mem_take
    simpa [
      qftZWork,
      Reg.take,
      Reg.drop
    ] using hq

  exact List.mem_of_mem_drop hqDrop


lemma qftXWork_qftZWork_disjoint
    {k : ℕ}
    (ops : Prog k)
    (r : ExtReg) :
    Disjoint
      (qftXWork ops r)
      (qftZWork ops r) := by
  rw [Disjoint, List.disjoint_left]
  intro q hqx hqz

  have hqxTake :
      q ∈
        r.reserve.qubits.take
          (qftWorkspaceNeed ops r.width).1 := by
    simpa [
      qftXWork,
      Reg.take
    ] using hqx

  have hqzDrop :
      q ∈
        r.reserve.qubits.drop
          (qftWorkspaceNeed ops r.width).1 := by
    apply List.mem_of_mem_take
    simpa [
      qftZWork,
      Reg.take,
      Reg.drop
    ] using hqz

  have hdisjoint :=
    List.disjoint_take_drop
      r.reserve.nodup
      (le_refl
        (qftWorkspaceNeed ops r.width).1)

  rw [List.disjoint_left] at hdisjoint
  exact hdisjoint hqxTake hqzDrop


@[simp] lemma regSize_qftXWork
    {k : ℕ}
    (ops : Prog k)
    (r : ExtReg)
    (hworkspace : QFTReserveOK ops r) :
    regSize (qftXWork ops r) =
      (qftWorkspaceNeed ops r.width).1 := by
  have hxFits :
      (qftWorkspaceNeed ops r.width).1
        ≤
      r.capacity := by
    have htotal :=
      hworkspace.reserve_large_enough
    omega

  simpa [
    qftXWork,
    Reg.take,
    regSize,
    Reg.width,
    ExtReg.capacity,
    Nat.min_eq_left hxFits
  ]


@[simp] lemma regSize_qftZWork
    {k : ℕ}
    (ops : Prog k)
    (r : ExtReg)
    (hworkspace : QFTReserveOK ops r) :
    regSize (qftZWork ops r) =
      (qftWorkspaceNeed ops r.width).2 := by
  have hzFits :
      (qftWorkspaceNeed ops r.width).2
        ≤
      r.capacity -
        (qftWorkspaceNeed ops r.width).1 := by
    have htotal :=
      hworkspace.reserve_large_enough
    omega

  simpa [
    qftZWork,
    Reg.take,
    Reg.drop,
    regSize,
    Reg.width,
    ExtReg.capacity,
    Nat.min_eq_left hzFits
  ]


namespace QFTReserveOK

lemma explicitWorkspace
    {k : ℕ}
    {ops : Prog k}
    {r : ExtReg}
    (hworkspace : QFTReserveOK ops r) :
    QFTWorkspaceOK
      ops
      r.active
      (qftXWork ops r)
      (qftZWork ops r) := by
  refine
    {
      data_x_disjoint := ?_
      data_z_disjoint := ?_
      work_disjoint :=
        qftXWork_qftZWork_disjoint ops r
      x_large_enough := ?_
      z_large_enough := ?_
    }

  ·
    apply disjoint_of_right_subset
      (fun q hq =>
        qftXWork_mem_reserve ops r hq)
    exact r.active_reserve_disjoint

  ·
    apply disjoint_of_right_subset
      (fun q hq =>
        qftZWork_mem_reserve ops r hq)
    exact r.active_reserve_disjoint

  ·
    rw [regSize_qftXWork ops r hworkspace]
    simp [ExtReg.width]

  ·
    rw [regSize_qftZWork ops r hworkspace]
    simp [ExtReg.width]

end QFTReserveOK


/-! =========================================================
    Section 4: Unfolding and bounds for `qftWorkspaceNeed`

    A nontrivial QFT split must reserve enough space for the middle phase
    product and both recursive QFT calls. These monotonicity lemmas let the
    plan constructor reuse the same workspace pools for each child.
========================================================= -/

lemma qftWorkspaceNeed_eq_of_two_le
    {k : ℕ}
    (ops : Prog k)
    (n : ℕ)
    (hn : 2 ≤ n) :
    qftWorkspaceNeed ops n =
      let leftWidth := n / 2
      let rightWidth := n - leftWidth

      let phaseNeed :=
        RecursivePhaseWorkspace.reserveNeed
          ops
          (leftWidth + 1)
          (rightWidth + 1)

      let leftNeed :=
        qftWorkspaceNeed ops leftWidth

      let rightNeed :=
        qftWorkspaceNeed ops rightWidth

      (
        max
          (1 + phaseNeed.1)
          (max leftNeed.1 rightNeed.1),

        max
          (1 + phaseNeed.2)
          (max leftNeed.2 rightNeed.2)
      ) := by
  cases n with
  | zero =>
      omega
  | succ n =>
      cases n with
      | zero =>
          omega
      | succ n =>
          conv_lhs =>
            unfold qftWorkspaceNeed


lemma qftWorkspaceNeed_phase_x_le
    {k : ℕ}
    (ops : Prog k)
    (n : ℕ)
    (hn : 2 ≤ n) :
    1 +
        (RecursivePhaseWorkspace.reserveNeed
          ops
          (n / 2 + 1)
          (n - n / 2 + 1)).1
      ≤
    (qftWorkspaceNeed ops n).1 := by
  rw [qftWorkspaceNeed_eq_of_two_le ops n hn]
  dsimp only
  exact Nat.le_max_left _ _


lemma qftWorkspaceNeed_phase_z_le
    {k : ℕ}
    (ops : Prog k)
    (n : ℕ)
    (hn : 2 ≤ n) :
    1 +
        (RecursivePhaseWorkspace.reserveNeed
          ops
          (n / 2 + 1)
          (n - n / 2 + 1)).2
      ≤
    (qftWorkspaceNeed ops n).2 := by
  rw [qftWorkspaceNeed_eq_of_two_le ops n hn]
  dsimp only
  exact Nat.le_max_left _ _


lemma qftWorkspaceNeed_left_x_le
    {k : ℕ}
    (ops : Prog k)
    (n : ℕ)
    (hn : 2 ≤ n) :
    (qftWorkspaceNeed ops (n / 2)).1
      ≤
    (qftWorkspaceNeed ops n).1 := by
  rw [qftWorkspaceNeed_eq_of_two_le ops n hn]
  dsimp only

  exact le_trans
    (Nat.le_max_left _ _)
    (Nat.le_max_right _ _)


lemma qftWorkspaceNeed_left_z_le
    {k : ℕ}
    (ops : Prog k)
    (n : ℕ)
    (hn : 2 ≤ n) :
    (qftWorkspaceNeed ops (n / 2)).2
      ≤
    (qftWorkspaceNeed ops n).2 := by
  rw [qftWorkspaceNeed_eq_of_two_le ops n hn]
  dsimp only

  exact le_trans
    (Nat.le_max_left _ _)
    (Nat.le_max_right _ _)


lemma qftWorkspaceNeed_right_x_le
    {k : ℕ}
    (ops : Prog k)
    (n : ℕ)
    (hn : 2 ≤ n) :
    (qftWorkspaceNeed ops (n - n / 2)).1
      ≤
    (qftWorkspaceNeed ops n).1 := by
  rw [qftWorkspaceNeed_eq_of_two_le ops n hn]
  dsimp only

  exact le_trans
    (Nat.le_max_right _ _)
    (Nat.le_max_right _ _)


lemma qftWorkspaceNeed_right_z_le
    {k : ℕ}
    (ops : Prog k)
    (n : ℕ)
    (hn : 2 ≤ n) :
    (qftWorkspaceNeed ops (n - n / 2)).2
      ≤
    (qftWorkspaceNeed ops n).2 := by
  rw [qftWorkspaceNeed_eq_of_two_le ops n hn]
  dsimp only

  exact le_trans
    (Nat.le_max_right _ _)
    (Nat.le_max_right _ _)


/-! =========================================================
    Section 5: Building child workspaces and recursive QFT plans

    The functions and lemmas below carve the two workspace pools into the
    pieces needed by the middle phase product and by the left/right recursive
    QFT calls. They culminate in the canonical plan and public lowered circuit.
========================================================= -/

lemma Gate.PhaseProdWorkspace.ownedDisjoint_grow
    {x z : Reg}
    (ws : Gate.PhaseProdWorkspace x z) :
    ExtReg.OwnedDisjoint
      (ws.xExt.grow 1)
      (ws.zExt.grow 1) := by
  unfold ExtReg.OwnedDisjoint

  rw [
    ExtReg.ownedQubits_grow,
    ExtReg.ownedQubits_grow
  ]

  change
    (x.qubits ++ ws.xReserve.qubits).Disjoint
      (z.qubits ++ ws.zReserve.qubits)

  rw [List.disjoint_left]
  intro q hqx hqz

  rw [List.mem_append] at hqx hqz

  rcases hqx with hqx | hqxReserve
  · rcases hqz with hqz | hqzReserve
    ·
      exact ws.xz_disjoint hqx hqz

    ·
      exact ws.zReserve_not_x hqzReserve hqx

  · rcases hqz with hqz | hqzReserve
    ·
      exact ws.xReserve_not_z hqxReserve hqz

    ·
      exact ws.reserve_disjoint hqxReserve hqzReserve

namespace QFTWorkspaceOK

variable
    {k : ℕ}
    {ops : Prog k}
    {r xWork zWork : Reg}


/--
Construct the concrete unsigned phase-product workspace at the current QFT
node from the two root workspace registers.
-/
noncomputable def phaseWorkspace
    (hworkspace :
      QFTWorkspaceOK ops r xWork zWork)
    (hsize : 2 ≤ regSize r) :
    Gate.PhaseProdWorkspace
      (leftReg r)
      (rightReg r) := by
  have hleftX :
      Disjoint (leftReg r) xWork := by
    apply disjoint_of_left_subset
      (fun q hq => leftReg_mem_parent r hq)
    exact hworkspace.data_x_disjoint

  have hleftZ :
      Disjoint (leftReg r) zWork := by
    apply disjoint_of_left_subset
      (fun q hq => leftReg_mem_parent r hq)
    exact hworkspace.data_z_disjoint

  have hrightX :
      Disjoint (rightReg r) xWork := by
    apply disjoint_of_left_subset
      (fun q hq => rightReg_mem_parent r hq)
    exact hworkspace.data_x_disjoint

  have hrightZ :
      Disjoint (rightReg r) zWork := by
    apply disjoint_of_left_subset
      (fun q hq => rightReg_mem_parent r hq)
    exact hworkspace.data_z_disjoint

  have hxNeed :
      1 ≤
        (qftWorkspaceNeed
          ops
          (regSize r)).1 := by
    have hphase :=
      qftWorkspaceNeed_phase_x_le
        ops
        (regSize r)
        hsize
    omega

  have hzNeed :
      1 ≤
        (qftWorkspaceNeed
          ops
          (regSize r)).2 := by
    have hphase :=
      qftWorkspaceNeed_phase_z_le
        ops
        (regSize r)
        hsize
    omega

  exact
    {
      xReserve := xWork
      zReserve := zWork

      x_can_grow :=
        le_trans
          hxNeed
          hworkspace.x_large_enough

      z_can_grow :=
        le_trans
          hzNeed
          hworkspace.z_large_enough

      xz_disjoint :=
        disjoint_left_right r

      x_reserve_disjoint :=
        hleftX

      z_reserve_disjoint :=
        hrightZ

      xReserve_not_z :=
        Disjoint.symm hrightX

      zReserve_not_x :=
        Disjoint.symm hleftZ

      reserve_disjoint :=
        hworkspace.work_disjoint
    }


/--
The root workspace bound implies sufficient signed-phase-product workspace at
the current QFT node.
-/
lemma signedWorkspaceOK
    (hworkspace :
      QFTWorkspaceOK ops r xWork zWork)
    (hsize : 2 ≤ regSize r) :
    let ws :=
      hworkspace.phaseWorkspace hsize

    SignedRecursiveWorkspaceOK
      ops
      (ws.xExt.grow 1)
      (ws.zExt.grow 1) := by
  dsimp only

  let ws :=
    hworkspace.phaseWorkspace hsize

  have hxWidth :
      (ws.xExt.grow 1).width =
        regSize (leftReg r) + 1 := by
    calc
      (ws.xExt.grow 1).width
          =
        ws.xExt.width + 1 := by
          exact
            ExtReg.width_grow
              ws.xExt
              1
              ws.xExt_canGrow

      _ =
        regSize (leftReg r) + 1 := by
          rfl

  have hzWidth :
      (ws.zExt.grow 1).width =
        regSize (rightReg r) + 1 := by
    calc
      (ws.zExt.grow 1).width
          =
        ws.zExt.width + 1 := by
          exact
            ExtReg.width_grow
              ws.zExt
              1
              ws.zExt_canGrow

      _ =
        regSize (rightReg r) + 1 := by
          rfl

  have hxCapacity :
      (ws.xExt.grow 1).capacity =
        regSize xWork - 1 := by
    calc
      (ws.xExt.grow 1).capacity
          =
        ws.xExt.capacity - 1 := by
          exact
            ExtReg.capacity_grow
              ws.xExt
              1
              ws.xExt_canGrow

      _ =
        regSize xWork - 1 := by
          rfl

  have hzCapacity :
      (ws.zExt.grow 1).capacity =
        regSize zWork - 1 := by
    calc
      (ws.zExt.grow 1).capacity
          =
        ws.zExt.capacity - 1 := by
          exact
            ExtReg.capacity_grow
              ws.zExt
              1
              ws.zExt_canGrow

      _ =
        regSize zWork - 1 := by
          rfl

  have hxPhaseBound :
      1 +
          (RecursivePhaseWorkspace.reserveNeed
            ops
            (regSize (leftReg r) + 1)
            (regSize (rightReg r) + 1)).1
        ≤
      regSize xWork := by
    rw [regSize_leftReg, regSize_rightReg]
    exact
      le_trans
        (qftWorkspaceNeed_phase_x_le
          ops
          (regSize r)
          hsize)
        hworkspace.x_large_enough

  have hzPhaseBound :
      1 +
          (RecursivePhaseWorkspace.reserveNeed
            ops
            (regSize (leftReg r) + 1)
            (regSize (rightReg r) + 1)).2
        ≤
      regSize zWork := by
    rw [regSize_leftReg, regSize_rightReg]
    exact
      le_trans
        (qftWorkspaceNeed_phase_z_le
          ops
          (regSize r)
          hsize)
        hworkspace.z_large_enough

  refine
    {
      owned_disjoint :=
        Gate.PhaseProdWorkspace.ownedDisjoint_grow
          ws

      x_reserve_sufficient := ?_

      z_reserve_sufficient := ?_
    }

  · rw [
      hxWidth,
      hzWidth,
      hxCapacity
    ]
    omega

  · rw [
      hxWidth,
      hzWidth,
      hzCapacity
    ]
    omega


/--
The root workspace condition remains valid for the left recursive QFT.
-/
lemma left
    (hworkspace :
      QFTWorkspaceOK ops r xWork zWork)
    (hsize : 2 ≤ regSize r) :
    QFTWorkspaceOK
      ops
      (leftReg r)
      xWork
      zWork := by
  refine
    {
      data_x_disjoint := ?_
      data_z_disjoint := ?_
      work_disjoint :=
        hworkspace.work_disjoint
      x_large_enough := ?_
      z_large_enough := ?_
    }

  ·
    apply disjoint_of_left_subset
      (fun q hq => leftReg_mem_parent r hq)
    exact hworkspace.data_x_disjoint

  ·
    apply disjoint_of_left_subset
      (fun q hq => leftReg_mem_parent r hq)
    exact hworkspace.data_z_disjoint

  ·
    simpa using
      (le_trans
        (qftWorkspaceNeed_left_x_le
          ops
          (regSize r)
          hsize)
        hworkspace.x_large_enough)

  ·
    simpa using
      (le_trans
        (qftWorkspaceNeed_left_z_le
          ops
          (regSize r)
          hsize)
        hworkspace.z_large_enough)

/--
The root workspace condition remains valid for the right recursive QFT.
-/
lemma right
    (hworkspace :
      QFTWorkspaceOK ops r xWork zWork)
    (hsize : 2 ≤ regSize r) :
    QFTWorkspaceOK
      ops
      (rightReg r)
      xWork
      zWork := by
  refine
    {
      data_x_disjoint := ?_
      data_z_disjoint := ?_
      work_disjoint :=
        hworkspace.work_disjoint
      x_large_enough := ?_
      z_large_enough := ?_
    }

  ·
    apply disjoint_of_left_subset
      (fun q hq => rightReg_mem_parent r hq)
    exact hworkspace.data_x_disjoint

  ·
    apply disjoint_of_left_subset
      (fun q hq => rightReg_mem_parent r hq)
    exact hworkspace.data_z_disjoint

  ·
    simpa using
      (le_trans
        (qftWorkspaceNeed_right_x_le
          ops
          (regSize r)
          hsize)
        hworkspace.x_large_enough)

  ·
    simpa using
      (le_trans
        (qftWorkspaceNeed_right_z_le
          ops
          (regSize r)
          hsize)
        hworkspace.z_large_enough)

end QFTWorkspaceOK

noncomputable def standardQFTLoweringPlan
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (r xWork zWork : Reg)
    (hworkspace :
      QFTWorkspaceOK ops r xWork zWork) :
    QFTLoweringPlan k hk ops r := by
  by_cases hzero : regSize r = 0

  · exact
      QFTLoweringPlan.empty r hzero

  · by_cases hone : regSize r = 1

    · exact
        QFTLoweringPlan.singleton r hone

    · have hlarge : 2 ≤ regSize r := by
        omega

      let ws :
          Gate.PhaseProdWorkspace
            (leftReg r)
            (rightReg r) :=
        hworkspace.phaseWorkspace hlarge

      have hphaseWorkspace :
          SignedRecursiveWorkspaceOK
            ops
            (ws.xExt.grow 1)
            (ws.zExt.grow 1) := by
        simpa [ws] using
          hworkspace.signedWorkspaceOK hlarge

      have hrightWorkspace :
          QFTWorkspaceOK
            ops
            (rightReg r)
            xWork
            zWork :=
        hworkspace.right hlarge

      have hleftWorkspace :
          QFTWorkspaceOK
            ops
            (leftReg r)
            xWork
            zWork :=
        hworkspace.left hlarge

      let phasePlan :
          StandardPhaseLoweringPlan
            k
            hk
            ops
            (phaseProdUsingInputSize ws)
            (Gate.PhaseProdUsing
              (qftPhi (regSize r))
              (leftReg r)
              (rightReg r)
              ws) :=
        standardPhaseProdUsingPlan
          k
          hk
          ops
          (qftPhi (regSize r))
          ws
          hphaseWorkspace

      let rightPlan :
          QFTLoweringPlan
            k hk ops
            (rightReg r) :=
        standardQFTLoweringPlan
          k
          hk
          ops
          (rightReg r)
          xWork
          zWork
          hrightWorkspace

      let leftPlan :
          QFTLoweringPlan
            k hk ops
            (leftReg r) :=
        standardQFTLoweringPlan
          k
          hk
          ops
          (leftReg r)
          xWork
          zWork
          hleftWorkspace

      exact
        QFTLoweringPlan.split
          r
          hlarge
          ws
          (phaseProdUsingInputSize ws)
          phasePlan
          rightPlan
          leftPlan

termination_by regSize r
decreasing_by
  ·
    have hhalfPos :
        0 < regSize r / 2 := by
      exact
        Nat.div_pos
          (by omega)
          (by decide)

    have hright :
        regSize r - regSize r / 2 <
          regSize r := by
      exact
        Nat.sub_lt
          (by omega)
          hhalfPos

    simpa [
      rightReg,
      halfSplitPoint,
      splitM
    ] using hright

  ·
    have hleft :
        regSize r / 2 <
          regSize r := by
      exact
        Nat.div_lt_self
          (by omega)
          (by decide)

    simpa [
      leftReg,
      halfSplitPoint,
      splitM
    ] using hleft

/--
Main reserve-plan theorem for this file.

The canonical plan obtained by splitting the inactive portion of `r`. This is
the bridge from the public reserve predicate `QFTReserveOK` to the recursive
QFT plan used by the low-level lowerer.
-/
noncomputable def reserveQFTLoweringPlan
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (r : ExtReg)
    (hworkspace : QFTReserveOK ops r) :
    QFTLoweringPlan k hk ops r.active :=
  standardQFTLoweringPlan
    k
    hk
    ops
    r.active
    (qftXWork ops r)
    (qftZWork ops r)
    hworkspace.explicitWorkspace


/--
Final public constructor for this file.

The canonical lowered QFT. Its workspace is selected deterministically from
`r.reserve`; callers do not supply separate physical workspace registers.
-/
noncomputable def lowerQFT
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (r : ExtReg)
    (hworkspace : QFTReserveOK ops r) :
    LowGate :=
  lowerQFTPlan
    (reserveQFTLoweringPlan
      k hk ops r hworkspace)


end Shor
