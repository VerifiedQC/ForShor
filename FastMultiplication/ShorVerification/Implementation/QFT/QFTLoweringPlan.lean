import FastMultiplication.ShorVerification.Implementation.QFT.DefsCore

/-!
# QFT Lowering Plan

The recursive lowering plan constructors (`phaseWorkspace`,
`standard*Plan`, `reserve*Plan`).  These bake their workspace obligations in, so
they carry the supporting lemmas they need.  Imports only `DefsCore`.
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

namespace Gate.PhaseProdWorkspace

end Gate.PhaseProdWorkspace

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


/-! =========================================================
    Section 2: Public QFT workspace sizes and clean-state predicates

    The public QFT lowerer takes one `ExtReg`. Its inactive reserve is split
    deterministically into an x-side pool and a z-side pool. The predicates in
    this section are the static and dynamic contracts for those pools.
========================================================= -/

namespace QFTWorkspaceCleanState
variable {qs : QSemantics} [RegEncoding qs.Basis] {xWork zWork : Reg}
end QFTWorkspaceCleanState

/-! =========================================================
    Section 3: Helper lemmas for the selected workspace slices

    These lemmas prove that the selected workspace registers have the requested
    sizes, remain inside the inactive reserve, and are disjoint from the active
    data register and from each other.
========================================================= -/

namespace QFTReserveOK

end QFTReserveOK


/-! =========================================================
    Section 4: Unfolding and bounds for `qftWorkspaceNeed`

    A nontrivial QFT split must reserve enough space for the middle phase
    product and both recursive QFT calls. These monotonicity lemmas let the
    plan constructor reuse the same workspace pools for each child.
========================================================= -/

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


end Shor
