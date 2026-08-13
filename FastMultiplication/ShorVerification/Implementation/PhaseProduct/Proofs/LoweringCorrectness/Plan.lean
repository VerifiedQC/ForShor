import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.LoweringCorrectness.Definitions
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Shared.GateConstructions

namespace Shor
open Gate
open Operations

/-!
# Phase-Product Lowering Plans
Finite lowering plans, their interpreter, syntactic plan lemmas, lowerability
facts, and canonical recursive plan construction for signed phase products.
-/

/-! =========================================================
    Section 1: Lowering plans
    A `PhaseLoweringPlan` is a finite certificate explaining how to replace a
    high-level gate with low-level gates. Primitive arithmetic gates lower
    directly, while signed phase products either stop at a naive base gate or
    recurse through a concrete compiled phase-product layout.
========================================================= -/

/-- Finite, structurally recursive plan for lowering one high-level gate. -/
inductive PhaseLoweringPlan
    (k : ℕ)
    (hk : 1 < k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (ops : Prog k) :
    ℕ → Gate → Type
  | id (initSize : ℕ) :
      PhaseLoweringPlan k hk pts hpts ops initSize Gate.id
  | seq
      {initSize : ℕ}
      {U V : Gate}
      (left : PhaseLoweringPlan k hk pts hpts ops initSize U)
      (right : PhaseLoweringPlan k hk pts hpts ops initSize V) :
      PhaseLoweringPlan k hk pts hpts ops initSize (U ;; V)

  | H
      (initSize : ℕ)
      (qbit : ℕ) :
      PhaseLoweringPlan k hk pts hpts ops initSize (Gate.H qbit)

  | X
      (initSize : ℕ)
      (qbit : ℕ) :
      PhaseLoweringPlan k hk pts hpts ops initSize (Gate.X qbit)

  | Prim
      (initSize : ℕ)
      (tag : String)
      (args : List ℕ) :
      PhaseLoweringPlan k hk pts hpts ops initSize (Gate.Prim tag args)

  | ShiftL
      (initSize : ℕ)
      (r : ExtReg)
      (n : ℕ) :
      PhaseLoweringPlan k hk pts hpts ops initSize (Gate.ShiftL r n)

  | ShiftR
      (initSize : ℕ)
      (r : ExtReg)
      (n : ℕ) :
      PhaseLoweringPlan k hk pts hpts ops initSize (Gate.ShiftR r n)

  | Negate
      (initSize : ℕ)
      (r : ExtReg) :
      PhaseLoweringPlan k hk pts hpts ops initSize (Gate.Negate r)

  | AddScaled
      (initSize : ℕ)
      (dst src : ExtReg)
      (negSrc : Bool)
      (shift : ℕ) :
      PhaseLoweringPlan k hk pts hpts ops initSize (Gate.AddScaled dst src negSrc shift)

  | zeroExtend
      (initSize : ℕ)
      (r : ExtReg)
      (n : ℕ) :
      PhaseLoweringPlan k hk pts hpts ops initSize (Gate.zeroExtend r n)

  | signExtend
      (initSize : ℕ)
      (r : ExtReg)
      (n : ℕ) :
      PhaseLoweringPlan k hk pts hpts ops initSize (Gate.signExtend r n)

  | zeroDealloc
      (initSize : ℕ)
      (r : ExtReg)
      (n : ℕ) :
      PhaseLoweringPlan k hk pts hpts ops initSize (Gate.zeroDealloc r n)

  | signDealloc
      (initSize : ℕ)
      (r : ExtReg)
      (n : ℕ) :
      PhaseLoweringPlan k hk pts hpts ops initSize (Gate.signDealloc r n)

  | RadixReverse
      (initSize : ℕ)
      (r : Reg)
      (m : ℕ) :
      PhaseLoweringPlan k hk pts hpts ops initSize (Gate.RadixReverse r m)

  /--
  The phase-product recursion has reached its base case.
  No allocation layout is needed because the base-case low-level phase-product
  implementation is used directly.
  -/
  | signedBase
      {initSize : ℕ}
      (phi : ℝ) (x z : ExtReg)
      (hstop : ¬ nextSignedWidth x z ops < initSize) :
      PhaseLoweringPlan k hk pts hpts ops initSize (Gate.SignedPhaseProd phi x z)
  /--
  A recursive signed phase-product step.
  `layout` specifies the physical chunk and reserve registers for this level.
  `hcapacity` proves this level can perform all required growth.
  `child` describes how the compiled circuit is recursively lowered.
  -/
  | signedStep
      {initSize : ℕ}
      (phi : ℝ)
      (x z : ExtReg)
      (layout : Gate.PhaseProductLayout x z k)
      (hrec : nextSignedWidth x z ops < initSize)
      (hcapacity : (initSignedLayoutState layout).CanGrowToNeeds (scanNeededWidths x z ops))
      (child : PhaseLoweringPlan k hk pts hpts ops (nextSignedWidth x z ops)
          (compiledSignedPhaseGate k hk pts hpts ops phi x z layout)) :
      PhaseLoweringPlan k hk pts hpts ops initSize (Gate.SignedPhaseProd phi x z)
  /--
  The controlled phase-product recursion has reached its base case.
  -/
  | cSignedBase
      {initSize : ℕ}
      (ctrl : ℕ)
      (phi : ℝ)
      (x z : ExtReg)
      (hstop :  ¬ nextSignedWidth x z ops < initSize) :
      PhaseLoweringPlan k hk pts hpts ops initSize (Gate.CSignedPhaseProd ctrl phi x z)
  /--
  A recursive controlled signed phase-product step.
  In addition to capacity, the control qubit must be outside every physical
  child register owned by the selected layout.
  -/
  | cSignedStep
      {initSize : ℕ}
      (ctrl : ℕ)
      (phi : ℝ)
      (x z : ExtReg)
      (layout : Gate.PhaseProductLayout x z k)
      (hrec : nextSignedWidth x z ops < initSize)
      (hcapacity : (initSignedLayoutState layout).CanGrowToNeeds (scanNeededWidths x z ops))
      (hctrl : layout.ControlDisjoint ctrl)
      (child : PhaseLoweringPlan k hk pts hpts ops (nextSignedWidth x z ops)
          (compiledCSignedPhaseGate k hk pts hpts ops ctrl phi x z layout)) :
      PhaseLoweringPlan k hk pts hpts ops initSize (Gate.CSignedPhaseProd ctrl phi x z)

/-! =========================================================
    Section 2: Plan-directed recursive lowering
    Interpreting a plan erases the proof data and returns the low-level gate
    chosen by the plan.
========================================================= -/

/--
Interpret a finite phase-lowering plan as a low-level circuit.
Termination is structural on `plan`. In a recursive phase-product case, the
child plan already contains the concrete layout and capacity proof required
for the next recursive call.
-/
noncomputable def lowerGateRec
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    {initSize : ℕ}
    {U : Gate}
    (plan : PhaseLoweringPlan k hk pts hpts ops initSize U) :
    LowGate := by
  induction plan with
  | id initSize => exact LowGate.id
  | seq left right ihLeft ihRight => exact LowGate.seq ihLeft ihRight
  | H initSize qbit => exact LowGate.H qbit
  | X initSize qbit => exact LowGate.X qbit
  | Prim initSize tag args => exact LowGate.Prim tag args
  | ShiftL initSize r n => exact LowGate.ShiftL r n
  | ShiftR initSize r n => exact LowGate.ShiftR r n
  | Negate initSize r => exact LowGate.Negate r
  | AddScaled initSize dst src negSrc shift => exact LowGate.AddScaled dst src negSrc shift
  | zeroExtend initSize r n => exact LowGate.zeroExtend r n
  | signExtend initSize r n => exact LowGate.signExtend r n
  | zeroDealloc initSize r n => exact LowGate.zeroDealloc r n
  | signDealloc initSize r n => exact LowGate.signDealloc r n
  | RadixReverse initSize r m => exact LowGate.RadixReverse r m
  | signedBase phi x z hstop => exact LowGate.Naive_SignedPhaseProd phi x z
  | signedStep phi x z layout hrec hcapacity child ihChild => exact ihChild
  | cSignedBase ctrl phi x z hstop => exact LowGate.Naive_CSignedPhaseProd ctrl phi x z
  | cSignedStep ctrl phi x z layout hrec hcapacity hctrl child ihChild => exact ihChild

/-! =========================================================
    Section 3: Standard interpolation-point plans
    Public helpers specialize the plan machinery to the canonical interpolation
    points used by the phase-product compiler.
========================================================= -/

/-- The generated interpolation-point list has the required size. -/
lemma generatedInterpolationPoints_length
    (k : ℕ) :
    (genInterpolationPoints k).length = q k := by
  simp [genInterpolationPoints, q]

/--
A lowering plan using the standard interpolation points.
This abbreviation hides the interpolation-point bookkeeping while leaving the
physical layout and workspace choices explicit in the plan.
-/
abbrev StandardPhaseLoweringPlan
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (initSize : ℕ)
    (U : Gate) :
    Type :=
  PhaseLoweringPlan k hk (genInterpolationPoints k) (generatedInterpolationPoints_length k)
    ops initSize  U

/-- Interpret a standard lowering plan for any gate in the supported fragment. -/
noncomputable def lowerPhasePlan
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    {initSize : ℕ}
    {U : Gate}
    (plan : StandardPhaseLoweringPlan k hk ops initSize U) :
    LowGate :=
  lowerGateRec plan

/--
Lower a signed phase product using a complete recursive workspace plan.
The plan is the precondition saying that every recursive call has:
* a concrete physical layout;
* sufficient reserve capacity;
* a strictly smaller recursive width.
-/
noncomputable def lowerSignedPhaseProd
    (k : ℕ)
    (hk : 1 < k)
    (phi : ℝ)
    (x z : ExtReg)
    (ops : Prog k)
    (plan : StandardPhaseLoweringPlan k hk ops (phaseInputSize x z)
      (Gate.SignedPhaseProd phi x z)) :
    LowGate :=
  lowerGateRec plan

/--
Lower a controlled signed phase product using a complete recursive workspace
plan. Controlled recursive steps additionally contain a
`layout.ControlDisjoint ctrl` proof.
-/
noncomputable def lowerCSignedPhaseProd
    (k : ℕ)
    (hk : 1 < k)
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (ops : Prog k)
    (plan : StandardPhaseLoweringPlan k hk ops (phaseInputSize x z)
        (Gate.CSignedPhaseProd ctrl phi x z)) :
    LowGate :=
  lowerGateRec plan

/-! =========================================================
    Section 4: Interpreter simp rules
========================================================= -/

namespace PhaseLoweringPlan

variable
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}

@[simp] lemma lowerGateRec_id
    (initSize : ℕ) :
    lowerGateRec
        (PhaseLoweringPlan.id
          (k := k)
          (hk := hk)
          (pts := pts)
          (hpts := hpts)
          (ops := ops)
          initSize)
      =
    LowGate.id := by
  rfl

@[simp] lemma lowerGateRec_seq
    {initSize : ℕ}
    {U V : Gate}
    (left :
      PhaseLoweringPlan
        k hk pts hpts ops initSize U)
    (right :
      PhaseLoweringPlan
        k hk pts hpts ops initSize V) :
    lowerGateRec
        (PhaseLoweringPlan.seq left right)
      =
    LowGate.seq
      (lowerGateRec left)
      (lowerGateRec right) := by
  rfl

@[simp] lemma lowerGateRec_signedBase
    {initSize : ℕ}
    (phi : ℝ)
    (x z : ExtReg)
    (hstop :
      ¬ nextSignedWidth x z ops < initSize) :
    lowerGateRec
        (PhaseLoweringPlan.signedBase
          (k := k)
          (hk := hk)
          (pts := pts)
          (hpts := hpts)
          (ops := ops)
          phi x z hstop)
      =
    LowGate.Naive_SignedPhaseProd phi x z := by
  rfl

@[simp] lemma lowerGateRec_signedStep
    {initSize : ℕ}
    (phi : ℝ)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (hrec :
      nextSignedWidth x z ops < initSize)
    (hcapacity :
      (initSignedLayoutState layout).CanGrowToNeeds
        (scanNeededWidths x z ops))
    (child :
      PhaseLoweringPlan
        k hk pts hpts ops
        (nextSignedWidth x z ops)
        (compiledSignedPhaseGate
          k hk pts hpts ops phi x z layout)) :
    lowerGateRec
        (PhaseLoweringPlan.signedStep
          (k := k)
          (hk := hk)
          (pts := pts)
          (hpts := hpts)
          (ops := ops)
          phi x z layout hrec hcapacity child)
      =
    lowerGateRec child := by
  rfl

@[simp] lemma lowerGateRec_cSignedBase
    {initSize : ℕ}
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (hstop :
      ¬ nextSignedWidth x z ops < initSize) :
    lowerGateRec
        (PhaseLoweringPlan.cSignedBase
          (k := k)
          (hk := hk)
          (pts := pts)
          (hpts := hpts)
          (ops := ops)
          ctrl phi x z hstop)
      =
    LowGate.Naive_CSignedPhaseProd ctrl phi x z := by
  rfl

@[simp] lemma lowerGateRec_cSignedStep
    {initSize : ℕ}
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (hrec :
      nextSignedWidth x z ops < initSize)
    (hcapacity :
      (initSignedLayoutState layout).CanGrowToNeeds
        (scanNeededWidths x z ops))
    (hctrl :
      layout.ControlDisjoint ctrl)
    (child :
      PhaseLoweringPlan
        k hk pts hpts ops
        (nextSignedWidth x z ops)
        (compiledCSignedPhaseGate
          k hk pts hpts ops
          ctrl phi x z layout)) :
    lowerGateRec
        (PhaseLoweringPlan.cSignedStep
          (k := k)
          (hk := hk)
          (pts := pts)
          (hpts := hpts)
          (ops := ops)
          ctrl phi x z layout
          hrec hcapacity hctrl child)
      =
    lowerGateRec child := by
  rfl

end PhaseLoweringPlan

/-! =========================================================
    Section 5: Lowerable-gate facts
========================================================= -/

namespace LowerablePhaseGate

@[simp] theorem not_adj
    (U : Gate) :
    ¬ LowerablePhaseGate (Gate.adj U) := by
  intro h; cases h

@[simp] theorem not_QFT
    (r : ExtReg) :
    ¬ LowerablePhaseGate (Gate.QFT r) := by
  intro h; cases h

/--
The concrete unsigned phase-product macro is in the lowerable fragment once
its physical two-qubit workspace has been supplied.
-/
theorem phaseProdUsing
    {x z : Reg}
    (phi : ℝ)
    (ws : Gate.PhaseProdWorkspace x z) :
    LowerablePhaseGate (Gate.PhaseProdUsing phi x z ws) := by
  unfold Gate.PhaseProdUsing
  exact LowerablePhaseGate.seq _ _ (LowerablePhaseGate.zeroExtend ws.xExt 1)
      (LowerablePhaseGate.seq _ _
        (LowerablePhaseGate.zeroExtend ws.zExt 1)
        (LowerablePhaseGate.seq _ _
          (LowerablePhaseGate.SignedPhaseProd
            phi
            (ws.xExt.grow 1)
            (ws.zExt.grow 1))
          (LowerablePhaseGate.seq _ _
            (LowerablePhaseGate.zeroDealloc ws.zExt 1)
            (LowerablePhaseGate.zeroDealloc ws.xExt 1))))

end LowerablePhaseGate

/-! =========================================================
    Section 6: Lowerability of compiled signed op lists
    These lemmas show that the circuits produced by the phase-product compiler
    are in the syntactic fragment supported by low-level lowering.
========================================================= -/

/-- Allocation chunk gates are in the lowerable fragment. -/
lemma lowerable_allocChunkGate
    {k : ℕ}
    (i : Fin k)
    (src dst : ExtReg) :
    LowerablePhaseGate
      (allocChunkGate i src dst) := by
  unfold allocChunkGate; simp
  split_ifs
  · simp [LowerablePhaseGate.id]
  · exact LowerablePhaseGate.signExtend src _
  · exact LowerablePhaseGate.zeroExtend src _

/-- Deallocation chunk gates are in the lowerable fragment. -/
lemma lowerable_deallocChunkGate
    {k : ℕ}
    (i : Fin k)
    (src dst : ExtReg) :
    LowerablePhaseGate
      (deallocChunkGate i src dst) := by
  unfold deallocChunkGate; simp
  split_ifs
  · exact LowerablePhaseGate.id
  · exact LowerablePhaseGate.signDealloc src _
  · exact LowerablePhaseGate.zeroDealloc src _

/-- Allocation prefixes are lowerable. -/
lemma lowerable_compileSignedAllocationsAux
    {k : ℕ}
    (src dst : LayoutState k) :
    ∀ (n : ℕ) (hn : n ≤ k),
      LowerablePhaseGate
        (compileSignedAllocationsAux src dst n hn) := by
  intro n hn
  induction n with
  | zero =>
      exact LowerablePhaseGate.id
  | succ n ih =>
      rw [compileSignedAllocationsAux_succ (src := src) (dst := dst) (n := n) (hn := hn)]
      let hn' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
      have htail : LowerablePhaseGate (compileSignedAllocationsAux src dst n hn') := ih hn'
      have hx : LowerablePhaseGate (allocChunkGate i (src.xslot i) (dst.xslot i)) := lowerable_allocChunkGate i (src.xslot i) (dst.xslot i)
      have hz : LowerablePhaseGate (allocChunkGate i (src.zslot i) (dst.zslot i)) := lowerable_allocChunkGate i (src.zslot i) (dst.zslot i)
      have hresult : LowerablePhaseGate
          (compileSignedAllocationsAux src dst n hn' ;; allocChunkGate i (src.xslot i) (dst.xslot i) ;;
            allocChunkGate i (src.zslot i) (dst.zslot i)) :=
        LowerablePhaseGate.seq _ _ htail (LowerablePhaseGate.seq _ _ hx hz)
      simpa [hn', i] using hresult

/-- Full signed allocation is lowerable. -/
lemma lowerable_compileSignedAllocations
    (k : ℕ)
    (src dst : LayoutState k) :
    LowerablePhaseGate
      (compileSignedAllocations k src dst) := by
  unfold compileSignedAllocations
  simpa using lowerable_compileSignedAllocationsAux (src := src) (dst := dst) k le_rfl

/-- Deallocation prefixes are lowerable. -/
lemma lowerable_compileSignedDeallocationsAux
    {k : ℕ}
    (src dst : LayoutState k) :
    ∀ (n : ℕ) (hn : n ≤ k),
      LowerablePhaseGate
        (compileSignedDeallocationsAux src dst n hn) := by
  intro n hn
  induction n with
  | zero =>
      exact LowerablePhaseGate.id
  | succ n ih =>
      rw [compileSignedDeallocationsAux_succ (src := src) (dst := dst) (n := n) (hn := hn)]
      let hn' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
      have hz :
          LowerablePhaseGate
            (deallocChunkGate
              i
              (src.zslot i)
              (dst.zslot i)) :=
        lowerable_deallocChunkGate
          i
          (src.zslot i)
          (dst.zslot i)
      have hx :
          LowerablePhaseGate
            (deallocChunkGate
              i
              (src.xslot i)
              (dst.xslot i)) :=
        lowerable_deallocChunkGate
          i
          (src.xslot i)
          (dst.xslot i)
      have htail : LowerablePhaseGate (compileSignedDeallocationsAux src dst n hn') := ih hn'
      have hresult :
          LowerablePhaseGate
            (deallocChunkGate
                i
                (src.zslot i)
                (dst.zslot i) ;;
              deallocChunkGate
                i
                (src.xslot i)
                (dst.xslot i) ;;
              compileSignedDeallocationsAux
                src dst n hn') :=
        LowerablePhaseGate.seq _ _
          hz
          (LowerablePhaseGate.seq _ _ hx htail)
      simpa [hn', i] using hresult

/-- Full signed deallocation is lowerable. -/
lemma lowerable_compileSignedDeallocations
    (k : ℕ)
    (src dst : LayoutState k) :
    LowerablePhaseGate
      (compileSignedDeallocations k src dst) := by
  unfold compileSignedDeallocations
  simpa using lowerable_compileSignedDeallocationsAux (src := src) (dst := dst) k le_rfl

/-- Compiled annotated operation bodies are lowerable. -/
lemma lowerable_compileAnnotatedOpsToSignedGateAux
    (k : ℕ)
    (hk : 1 < k)
    (phi : ℝ)
    (phaseCoeff : Fin (q k) → ℚ)
    (st : LayoutState k)
    (ops : List (AnnotatedOp k)) :
    LowerablePhaseGate
      (compileAnnotatedOpsToSignedGateAux
        k hk phi phaseCoeff st ops) := by
  induction ops generalizing st with
  | nil =>
      exact LowerablePhaseGate.id
  | cons annotated rest ih =>
      rcases annotated with ⟨op, phaseTerm?⟩
      cases op <;>
        cases phaseTerm? <;>
        simp [
          compileAnnotatedOpsToSignedGateAux,
          ih,
          LowerablePhaseGate.seq,
          LowerablePhaseGate.ShiftL,
          LowerablePhaseGate.ShiftR,
          LowerablePhaseGate.Negate,
          LowerablePhaseGate.AddScaled,
          LowerablePhaseGate.SignedPhaseProd
        ]

/-- The full compiled signed phase-product circuit is lowerable. -/
lemma lowerable_compileOpsToSignedGate
    (k : ℕ)
    (hk : 1 < k)
    (phi : ℝ)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (coeff : Fin (q k) → ℚ)
    (ops : Prog k) :
    LowerablePhaseGate
      (compileOpsToSignedGate
        k hk phi x z layout coeff ops) := by
  let need : NeededWidths k := scanNeededWidths x z ops
  let stInit : LayoutState k := initSignedLayoutState layout
  let stFinal : LayoutState k := targetSignedLayoutState stInit need
  change
    LowerablePhaseGate
      (compileSignedAllocations k stInit stFinal ;;
        compileAnnotatedOpsToSignedGateAux
          k hk phi coeff stFinal
          (annotatePhaseTermsAux k 0 ops) ;;
        compileSignedDeallocations k stInit stFinal)
  exact
    LowerablePhaseGate.seq _ _
      (lowerable_compileSignedAllocations
        k stInit stFinal)
      (LowerablePhaseGate.seq _ _
        (lowerable_compileAnnotatedOpsToSignedGateAux
          k hk phi coeff stFinal
          (annotatePhaseTermsAux k 0 ops))
        (lowerable_compileSignedDeallocations
          k stInit stFinal))

/-- The packaged compiled signed phase-product replacement is lowerable. -/
lemma lowerable_compiledSignedPhaseGate
    (k : ℕ)
    (hk : 1 < k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (ops : Prog k)
    (phi : ℝ)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k) :
    LowerablePhaseGate
      (compiledSignedPhaseGate
        k hk pts hpts ops phi x z layout) := by
  unfold compiledSignedPhaseGate
  exact lowerable_compileOpsToSignedGate k hk phi x z layout (loweringPhaseCoeff k x z pts hpts) ops

/-- Control-phase wrapping preserves lowerability. -/
lemma lowerable_controlPhaseLeaves
    (ctrl : ℕ)
    {U : Gate}
    (hU : LowerablePhaseGate U) :
    LowerablePhaseGate
      (controlPhaseLeaves ctrl U) := by
  induction hU with
  | id =>
      exact LowerablePhaseGate.id
  | seq U V hU hV ihU ihV =>
      exact LowerablePhaseGate.seq _ _ ihU ihV
  | H qbit =>
      exact LowerablePhaseGate.H qbit
  | X qbit =>
      exact LowerablePhaseGate.X qbit
  | Prim tag args =>
      exact LowerablePhaseGate.Prim tag args
  | ShiftL r n =>
      exact LowerablePhaseGate.ShiftL r n
  | ShiftR r n =>
      exact LowerablePhaseGate.ShiftR r n
  | Negate r =>
      exact LowerablePhaseGate.Negate r
  | AddScaled dst src negSrc shift =>
      exact
        LowerablePhaseGate.AddScaled
          dst src negSrc shift
  | SignedPhaseProd phi x z =>
      exact
        LowerablePhaseGate.CSignedPhaseProd
          ctrl phi x z
  | CSignedPhaseProd ctrl' phi x z =>
      exact
        LowerablePhaseGate.CSignedPhaseProd
          ctrl' phi x z
  | zeroExtend r n =>
      exact LowerablePhaseGate.zeroExtend r n
  | signExtend r n =>
      exact LowerablePhaseGate.signExtend r n
  | zeroDealloc r n =>
      exact LowerablePhaseGate.zeroDealloc r n
  | signDealloc r n =>
      exact LowerablePhaseGate.signDealloc r n
  | RadixReverse r m =>
      exact LowerablePhaseGate.RadixReverse r m

/-- The full compiled controlled signed phase-product circuit is lowerable. -/
lemma lowerable_compileOpsToCSignedGate
    (k : ℕ)
    (hk : 1 < k)
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (coeff : Fin (q k) → ℚ)
    (ops : Prog k) :
    LowerablePhaseGate
      (compileOpsToCSignedGate
        k hk ctrl phi x z layout coeff ops) := by
  unfold compileOpsToCSignedGate
  exact lowerable_controlPhaseLeaves ctrl (lowerable_compileOpsToSignedGate k hk phi x z layout coeff ops)

/-- The packaged compiled controlled phase-product replacement is lowerable. -/
lemma lowerable_compiledCSignedPhaseGate
    (k : ℕ)
    (hk : 1 < k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (ops : Prog k)
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k) :
    LowerablePhaseGate
      (compiledCSignedPhaseGate
        k hk pts hpts ops
        ctrl phi x z layout) := by
  unfold compiledCSignedPhaseGate
  exact lowerable_compileOpsToCSignedGate k hk ctrl phi x z layout (loweringPhaseCoeff k x z pts hpts) ops

/-! =========================================================
    Section 7: Plans for compiled allocation and body gates
    The definitions below mirror the compiler constructors, replacing each gate
    with the corresponding plan node and threading recursive phase-product plans
    through phase-product leaves.
========================================================= -/

/-- Plan for the allocation gate generated for one chunk. -/
noncomputable def planAllocChunkGate
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    (initSize : ℕ)
    (i : Fin k)
    (src dst : ExtReg) :
    PhaseLoweringPlan k hk pts hpts ops initSize (allocChunkGate i src dst) := by
  unfold allocChunkGate
  dsimp
  split
  · exact PhaseLoweringPlan.id initSize
  · split
    · exact
        PhaseLoweringPlan.signExtend initSize src (extraDelta src dst)
    · exact
        PhaseLoweringPlan.zeroExtend initSize src (extraDelta src dst)

/-- Plan for the deallocation gate generated for one chunk. -/
noncomputable def planDeallocChunkGate
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    (initSize : ℕ)
    (i : Fin k)
    (src dst : ExtReg) :
    PhaseLoweringPlan
      k hk pts hpts ops
      initSize
      (deallocChunkGate i src dst) := by
  unfold deallocChunkGate
  dsimp
  split
  · exact PhaseLoweringPlan.id initSize
  · split
    · exact
        PhaseLoweringPlan.signDealloc initSize src (extraDelta src dst)
    · exact
        PhaseLoweringPlan.zeroDealloc initSize src (extraDelta src dst)

/-- Plan for an allocation prefix. -/
noncomputable def planCompileSignedAllocationsAux
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    (initSize : ℕ)
    (src dst : LayoutState k) :
    ∀ (n : ℕ) (hn : n ≤ k),
      PhaseLoweringPlan k hk pts hpts ops initSize (compileSignedAllocationsAux src dst n hn)
  | 0, _ =>
      PhaseLoweringPlan.id initSize
  | n + 1, hn =>
      let hn' : n ≤ k :=  Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn

      let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩

      let previous := planCompileSignedAllocationsAux initSize src dst n hn'

      let planX :=
        planAllocChunkGate (initSize := initSize) i (src.xslot i) (dst.xslot i)

      let planZ :=
        planAllocChunkGate (initSize := initSize) i (src.zslot i) (dst.zslot i)

      PhaseLoweringPlan.seq previous (PhaseLoweringPlan.seq planX planZ)

/-- Plan for the full signed allocation circuit. -/
noncomputable def planCompileSignedAllocations
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    (initSize : ℕ)
    (src dst : LayoutState k) :
    PhaseLoweringPlan k hk pts hpts ops initSize
      (compileSignedAllocations k src dst) := by
  unfold compileSignedAllocations
  exact planCompileSignedAllocationsAux initSize src dst k le_rfl

/-- Plan for a deallocation prefix. -/
noncomputable def planCompileSignedDeallocationsAux
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    (initSize : ℕ)
    (src dst : LayoutState k) :
    ∀ (n : ℕ) (hn : n ≤ k),
      PhaseLoweringPlan k hk pts hpts ops initSize
        (compileSignedDeallocationsAux src dst n hn)
  | 0, _ =>
      PhaseLoweringPlan.id initSize
  | n + 1, hn =>
      let hn' : n ≤ k :=  Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn

      let i : Fin k := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩

      let planZ := planDeallocChunkGate (initSize := initSize) i (src.zslot i) (dst.zslot i)

      let planX :=  planDeallocChunkGate (initSize := initSize) i (src.xslot i)  (dst.xslot i)

      let previous := planCompileSignedDeallocationsAux initSize src dst n hn'

      PhaseLoweringPlan.seq planZ (PhaseLoweringPlan.seq planX previous)

/-- Plan for the full signed deallocation circuit. -/
noncomputable def planCompileSignedDeallocations
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    (initSize : ℕ)
    (src dst : LayoutState k) :
    PhaseLoweringPlan  k hk pts hpts ops initSize
      (compileSignedDeallocations k src dst) := by
  unfold compileSignedDeallocations
  exact planCompileSignedDeallocationsAux initSize src dst k le_rfl

/-- Plan for the annotated body circuit, using `recurse` at phase-product leaves. -/
noncomputable def planCompileAnnotatedOpsToSignedGateAux
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    (initSize : ℕ)
    (phi : ℝ)
    (phaseCoeff : Fin (q k) → ℚ)
    (st : LayoutState k)
    (recurse :
      ∀ (i : Fin k) (theta : ℝ),
        PhaseLoweringPlan k hk pts hpts ops initSize
          (Gate.SignedPhaseProd theta (st.xslot i) (st.zslot i))) :
    ∀ annotatedOps : List (AnnotatedOp k),
      PhaseLoweringPlan k hk pts hpts ops initSize
        (compileAnnotatedOpsToSignedGateAux k hk phi phaseCoeff st annotatedOps)
  | [] =>
      PhaseLoweringPlan.id initSize
  | ⟨op, phaseTerm?⟩ :: rest =>
      let tail :=
        planCompileAnnotatedOpsToSignedGateAux initSize phi phaseCoeff st recurse rest

      match op with
      | .shiftL i n =>
          PhaseLoweringPlan.seq (PhaseLoweringPlan.ShiftL initSize (st.xslot i) n)
            (PhaseLoweringPlan.seq (PhaseLoweringPlan.ShiftL initSize (st.zslot i) n) tail)

      | .shiftR i n =>
          PhaseLoweringPlan.seq
            (PhaseLoweringPlan.ShiftR initSize (st.xslot i) n)
            (PhaseLoweringPlan.seq (PhaseLoweringPlan.ShiftR initSize (st.zslot i) n) tail)

      | .negate i =>
          PhaseLoweringPlan.seq
            (PhaseLoweringPlan.Negate initSize (st.xslot i))
            (PhaseLoweringPlan.seq (PhaseLoweringPlan.Negate initSize (st.zslot i)) tail)

      | .addScaled dst src negSrc shift =>
          PhaseLoweringPlan.seq
            (PhaseLoweringPlan.AddScaled initSize (st.xslot dst) (st.xslot src) negSrc shift)
            (PhaseLoweringPlan.seq
              (PhaseLoweringPlan.AddScaled initSize
                (st.zslot dst) (st.zslot src) negSrc shift)
              tail)

      | .phaseProduct i =>
          match phaseTerm? with
          | some l =>
              PhaseLoweringPlan.seq (recurse i (phi * (((phaseCoeff l : ℚ) : ℝ)))) tail
          | none =>
              tail

/-- Plan for the controlled annotated body circuit, using `recurse` at controlled phase-product leaves. -/
noncomputable def planCompileAnnotatedOpsToCSignedGateAux
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    (initSize : ℕ)
    (ctrl : ℕ)
    (phi : ℝ)
    (phaseCoeff : Fin (q k) → ℚ)
    (st : LayoutState k)
    (recurse :
      ∀ (i : Fin k) (theta : ℝ),
        PhaseLoweringPlan k hk pts hpts ops initSize
          (Gate.CSignedPhaseProd ctrl theta (st.xslot i) (st.zslot i))) :
    ∀ annotatedOps : List (AnnotatedOp k),
      PhaseLoweringPlan k hk pts hpts ops initSize
        (controlPhaseLeaves ctrl
          (compileAnnotatedOpsToSignedGateAux k hk phi phaseCoeff st annotatedOps))
  | [] =>
      PhaseLoweringPlan.id initSize
  | ⟨op, phaseTerm?⟩ :: rest =>
      let tail :=
        planCompileAnnotatedOpsToCSignedGateAux initSize ctrl phi phaseCoeff st recurse rest
      match op with
      | .shiftL i n =>
          PhaseLoweringPlan.seq (PhaseLoweringPlan.ShiftL initSize (st.xslot i) n)
            (PhaseLoweringPlan.seq (PhaseLoweringPlan.ShiftL initSize (st.zslot i) n) tail)
      | .shiftR i n =>
          PhaseLoweringPlan.seq (PhaseLoweringPlan.ShiftR initSize (st.xslot i) n)
            (PhaseLoweringPlan.seq (PhaseLoweringPlan.ShiftR initSize (st.zslot i) n) tail)
      | .negate i =>
          PhaseLoweringPlan.seq (PhaseLoweringPlan.Negate initSize (st.xslot i))
            (PhaseLoweringPlan.seq (PhaseLoweringPlan.Negate initSize (st.zslot i)) tail)
      | .addScaled dst src negSrc shift =>
          PhaseLoweringPlan.seq
            (PhaseLoweringPlan.AddScaled initSize (st.xslot dst) (st.xslot src) negSrc shift)
            (PhaseLoweringPlan.seq
              (PhaseLoweringPlan.AddScaled initSize (st.zslot dst) (st.zslot src) negSrc shift)
              tail)
      | .phaseProduct i =>
          match phaseTerm? with
          | some l =>
              PhaseLoweringPlan.seq (recurse i (phi * (((phaseCoeff l : ℚ) : ℝ)))) tail
          | none =>
              tail

/-! =========================================================
    Section 8: Public recursive signed phase-product plans
========================================================= -/

/-- Plan for the compiled signed phase-product replacement at one recursive level. -/
noncomputable def planCompiledSignedPhaseGate
    {k : ℕ}
    (hk : 1 < k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (ops : Prog k)
    (phi : ℝ)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (recurse :
      let src :=
        initSignedLayoutState layout
      let dst :=
        targetSignedLayoutState
          src
          (scanNeededWidths x z ops)
      ∀ (i : Fin k) (theta : ℝ),
        PhaseLoweringPlan
          k hk pts hpts ops
          (nextSignedWidth x z ops)
          (Gate.SignedPhaseProd
            theta
            (dst.xslot i)
            (dst.zslot i))) :
    PhaseLoweringPlan
      k hk pts hpts ops
      (nextSignedWidth x z ops)
      (compiledSignedPhaseGate
        k hk pts hpts ops
        phi x z layout) := by
  let need : NeededWidths k :=
    scanNeededWidths x z ops
  let src : LayoutState k :=
    initSignedLayoutState layout
  let dst : LayoutState k :=
    targetSignedLayoutState src need
  let coeff : Fin (q k) → ℚ :=
    loweringPhaseCoeff
      k x z pts hpts
  let annotatedOps : List (AnnotatedOp k) :=
    annotatePhaseTermsAux k 0 ops
  have recurse' :
      ∀ (i : Fin k) (theta : ℝ),
        PhaseLoweringPlan
          k hk pts hpts ops
          (nextSignedWidth x z ops)
          (Gate.SignedPhaseProd
            theta
            (dst.xslot i)
            (dst.zslot i)) := by
    simpa [src, dst, need] using recurse
  let allocationPlan :
      PhaseLoweringPlan
        k hk pts hpts ops
        (nextSignedWidth x z ops)
        (compileSignedAllocations
          k src dst) :=
    planCompileSignedAllocations
      (nextSignedWidth x z ops)
      src
      dst
  let bodyPlan :
      PhaseLoweringPlan k hk pts hpts ops
        (nextSignedWidth x z ops)
        (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst annotatedOps) :=
    planCompileAnnotatedOpsToSignedGateAux (nextSignedWidth x z ops)
      phi coeff dst recurse' annotatedOps
  let deallocationPlan :
      PhaseLoweringPlan k hk pts hpts ops
        (nextSignedWidth x z ops)
        (compileSignedDeallocations k src dst) :=
    planCompileSignedDeallocations (nextSignedWidth x z ops) src dst
  have completePlan :
      PhaseLoweringPlan
        k hk pts hpts ops
        (nextSignedWidth x z ops)
        (
          compileSignedAllocations k src dst
          ;;
          compileAnnotatedOpsToSignedGateAux
            k hk phi coeff dst annotatedOps
          ;;
          compileSignedDeallocations k src dst
        ) :=
    PhaseLoweringPlan.seq
      allocationPlan
      (PhaseLoweringPlan.seq
        bodyPlan
        deallocationPlan)
  simpa [
    compiledSignedPhaseGate,
    compileOpsToSignedGate,
    src,
    dst,
    need,
    coeff,
    annotatedOps
  ] using completePlan

/-- Plan for the compiled controlled signed phase-product replacement at one recursive level. -/
noncomputable def planCompiledCSignedPhaseGate
    {k : ℕ}
    (hk : 1 < k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (ops : Prog k)
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (recurse :
      let src := initSignedLayoutState layout
      let dst := targetSignedLayoutState src (scanNeededWidths x z ops)
      ∀ (i : Fin k) (theta : ℝ),
        PhaseLoweringPlan k hk pts hpts ops (nextSignedWidth x z ops)
          (Gate.CSignedPhaseProd ctrl theta (dst.xslot i) (dst.zslot i))) :
    PhaseLoweringPlan k hk pts hpts ops (nextSignedWidth x z ops)
      (compiledCSignedPhaseGate k hk pts hpts ops ctrl phi x z layout) := by
  let need : NeededWidths k := scanNeededWidths x z ops
  let src : LayoutState k := initSignedLayoutState layout
  let dst : LayoutState k := targetSignedLayoutState src need
  let coeff : Fin (q k) → ℚ := loweringPhaseCoeff k x z pts hpts
  let annotatedOps : List (AnnotatedOp k) := annotatePhaseTermsAux k 0 ops
  have recurse' :
      ∀ (i : Fin k) (theta : ℝ),
        PhaseLoweringPlan k hk pts hpts ops (nextSignedWidth x z ops)
          (Gate.CSignedPhaseProd ctrl theta (dst.xslot i) (dst.zslot i)) := by
    simpa [src, dst, need] using recurse
  let allocationPlan :
      PhaseLoweringPlan k hk pts hpts ops (nextSignedWidth x z ops)
        (compileSignedAllocations k src dst) :=
    planCompileSignedAllocations (nextSignedWidth x z ops) src dst
  let bodyPlan :
      PhaseLoweringPlan k hk pts hpts ops (nextSignedWidth x z ops)
        (controlPhaseLeaves ctrl
          (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst annotatedOps)) :=
    planCompileAnnotatedOpsToCSignedGateAux (nextSignedWidth x z ops)
      ctrl phi coeff dst recurse' annotatedOps
  let deallocationPlan :
      PhaseLoweringPlan k hk pts hpts ops (nextSignedWidth x z ops)
        (compileSignedDeallocations k src dst) :=
    planCompileSignedDeallocations (nextSignedWidth x z ops) src dst
  have completePlan :
      PhaseLoweringPlan k hk pts hpts ops (nextSignedWidth x z ops)
        (compileSignedAllocations k src dst ;;
          controlPhaseLeaves ctrl
            (compileAnnotatedOpsToSignedGateAux k hk phi coeff dst annotatedOps) ;;
          compileSignedDeallocations k src dst) :=
    PhaseLoweringPlan.seq allocationPlan (PhaseLoweringPlan.seq bodyPlan deallocationPlan)
  simpa [compiledCSignedPhaseGate, compileOpsToCSignedGate, compileOpsToSignedGate,
    controlPhaseLeaves, controlPhaseLeaves_compileSignedAllocations,
    controlPhaseLeaves_compileSignedDeallocations, src, dst, need, coeff, annotatedOps]
    using completePlan

/-- Canonical recursive plan for a signed phase product from static recursive workspace data. -/
noncomputable def standardSignedPhaseLoweringPlan
    (k : ℕ)
    (hk : 1 < k)
    (phi : ℝ)
    (x z : ExtReg)
    (ops : Prog k)
    (hworkspace : SignedRecursiveWorkspaceOK ops x z) :
    StandardPhaseLoweringPlan k hk ops (phaseInputSize x z) (Gate.SignedPhaseProd phi x z) := by
  by_cases hrec :
      nextSignedWidth x z ops <
        phaseInputSize x z
  · let step :
        CanonicalSignedStep ops x z :=
      canonicalSignedStep
        hk ops x z hrec hworkspace
    let src : LayoutState k :=
      initSignedLayoutState step.layout
    let dst : LayoutState k :=
      targetSignedLayoutState
        src
        (scanNeededWidths x z ops)
    have recurse :
        ∀ (i : Fin k) (theta : ℝ),
          PhaseLoweringPlan
            k
            hk
            (genInterpolationPoints k)
            (generatedInterpolationPoints_length k)
            ops
            (nextSignedWidth x z ops)
            (Gate.SignedPhaseProd
              theta
              (dst.xslot i)
              (dst.zslot i)) := by
      intro i theta
      have hchild :
          SignedRecursiveWorkspaceOK
            ops
            (dst.xslot i)
            (dst.zslot i) := by
        simpa [src, dst] using
          step.childWorkspace i
      have childPlan :=
        standardSignedPhaseLoweringPlan
          k
          hk
          theta
          (dst.xslot i)
          (dst.zslot i)
          ops
          hchild
      have hsize :
          phaseInputSize
              (dst.xslot i)
              (dst.zslot i)
            =
          nextSignedWidth x z ops := by
        simpa [src, dst] using
          step.childInputSize i
      simpa [hsize] using childPlan
    let child :
        PhaseLoweringPlan
          k
          hk
          (genInterpolationPoints k)
          (generatedInterpolationPoints_length k)
          ops
          (nextSignedWidth x z ops)
          (compiledSignedPhaseGate
            k
            hk
            (genInterpolationPoints k)
            (generatedInterpolationPoints_length k)
            ops
            phi
            x
            z
            step.layout) :=
      planCompiledSignedPhaseGate
        hk
        (genInterpolationPoints k)
        (generatedInterpolationPoints_length k)
        ops
        phi
        x
        z
        step.layout
        (by simpa [src, dst] using recurse)
    exact
      PhaseLoweringPlan.signedStep
        (k := k)
        (hk := hk)
        (pts := genInterpolationPoints k)
        (hpts :=
          generatedInterpolationPoints_length k)
        (ops := ops)
        phi
        x
        z
        step.layout
        hrec
        step.capacity
        child
  · exact
      PhaseLoweringPlan.signedBase
        (k := k)
        (hk := hk)
        (pts := genInterpolationPoints k)
        (hpts :=
          generatedInterpolationPoints_length k)
        (ops := ops)
        phi
        x
        z
        hrec
termination_by phaseInputSize x z
decreasing_by
  have hsize :
      phaseInputSize
          (dst.xslot i)
          (dst.zslot i)
        =
      nextSignedWidth x z ops := by
    simpa [src, dst] using
      step.childInputSize i
  rw [hsize]
  exact hrec

/-- Canonical recursive plan for a controlled signed phase product from static recursive workspace data. -/
noncomputable def standardCSignedPhaseLoweringPlan
    (k : ℕ)
    (hk : 1 < k)
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (ops : Prog k)
    (hworkspace : CSignedRecursiveWorkspaceOK ops ctrl x z) :
    StandardPhaseLoweringPlan k hk ops (phaseInputSize x z) (Gate.CSignedPhaseProd ctrl phi x z) := by
  by_cases hrec : nextSignedWidth x z ops < phaseInputSize x z
  · let step : CanonicalSignedStep ops x z :=
      canonicalSignedStep hk ops x z hrec hworkspace.toSignedRecursiveWorkspaceOK
    let src : LayoutState k := initSignedLayoutState step.layout
    let dst : LayoutState k := targetSignedLayoutState src (scanNeededWidths x z ops)
    have recurse :
        ∀ (i : Fin k) (theta : ℝ),
          PhaseLoweringPlan k hk (genInterpolationPoints k) (generatedInterpolationPoints_length k)
            ops (nextSignedWidth x z ops)
            (Gate.CSignedPhaseProd ctrl theta (dst.xslot i) (dst.zslot i)) := by
      intro i theta
      have hchildSigned :
          SignedRecursiveWorkspaceOK ops (dst.xslot i) (dst.zslot i) := by
        simpa [src, dst] using step.childWorkspace i
      have hctrlLayout : step.layout.ControlDisjoint ctrl :=
        step.layout.controlDisjoint_of_ctrlDisjoint hworkspace.control_disjoint
      have hctrlDst := controlDisjoint_target step.layout ctrl (scanNeededWidths x z ops) hctrlLayout
      have hchild :
          CSignedRecursiveWorkspaceOK ops ctrl (dst.xslot i) (dst.zslot i) :=
        { toSignedRecursiveWorkspaceOK := hchildSigned
          control_disjoint := by
            constructor
            · exact (by simpa [src, dst] using hctrlDst.1 i)
            · exact (by simpa [src, dst] using hctrlDst.2 i) }
      have childPlan :=
        standardCSignedPhaseLoweringPlan k hk ctrl theta (dst.xslot i) (dst.zslot i) ops hchild
      have hsize : phaseInputSize (dst.xslot i) (dst.zslot i) = nextSignedWidth x z ops := by
        simpa [src, dst] using step.childInputSize i
      simpa [hsize] using childPlan
    let child :
        PhaseLoweringPlan k hk (genInterpolationPoints k) (generatedInterpolationPoints_length k)
          ops (nextSignedWidth x z ops)
          (compiledCSignedPhaseGate k hk (genInterpolationPoints k)
            (generatedInterpolationPoints_length k) ops ctrl phi x z step.layout) :=
      planCompiledCSignedPhaseGate hk (genInterpolationPoints k)
        (generatedInterpolationPoints_length k) ops ctrl phi x z step.layout
        (by simpa [src, dst] using recurse)
    exact
      PhaseLoweringPlan.cSignedStep
        (k := k)
        (hk := hk)
        (pts := genInterpolationPoints k)
        (hpts := generatedInterpolationPoints_length k)
        (ops := ops)
        ctrl phi x z step.layout hrec step.capacity
        (step.layout.controlDisjoint_of_ctrlDisjoint hworkspace.control_disjoint)
        child
  · exact
      PhaseLoweringPlan.cSignedBase
        (k := k)
        (hk := hk)
        (pts := genInterpolationPoints k)
        (hpts := generatedInterpolationPoints_length k)
        (ops := ops)
        ctrl phi x z hrec
termination_by phaseInputSize x z
decreasing_by
  have hsize : phaseInputSize (dst.xslot i) (dst.zslot i) = nextSignedWidth x z ops := by
    simpa [src, dst] using step.childInputSize i
  rw [hsize]
  exact hrec

end Shor
