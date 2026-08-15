import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Defs
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.GateLevelCorrectness.GateConstructions
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.LoweringCorrectness.EvalLLemmas

/-!
# Phase-Product Lowerability

The `LowerablePhaseGate` predicate and the `lowerable_*` lemmas proving that each
gate produced by the phase-product compiler inhabits it.
-/


namespace Shor
open Gate
open Operations

/-! =========================================================
    Lowerable Gate Predicate

    This syntax-directed predicate records exactly the high-level gates that the
    phase-product lowering interpreter knows how to translate.
========================================================= -/

/-- High-level gates that the phase-product lowering pipeline knows how to lower. -/
inductive LowerablePhaseGate : Gate → Prop where
  | id :
      LowerablePhaseGate Gate.id
  | seq :
      ∀ (U V : Gate),
        LowerablePhaseGate U →
        LowerablePhaseGate V →
        LowerablePhaseGate (Gate.seq U V)
  | H :
      ∀ qbit,
        LowerablePhaseGate (Gate.H qbit)
  | X :
      ∀ qbit,
        LowerablePhaseGate (Gate.X qbit)
  | Prim :
      ∀ tag args,
        LowerablePhaseGate (Gate.Prim tag args)
  | ShiftL :
      ∀ r n,
        LowerablePhaseGate (Gate.ShiftL r n)
  | ShiftR :
      ∀ r n,
        LowerablePhaseGate (Gate.ShiftR r n)
  | Negate :
      ∀ r,
        LowerablePhaseGate (Gate.Negate r)
  | AddScaled :
      ∀ dst src negSrc shift,
        LowerablePhaseGate (Gate.AddScaled dst src negSrc shift)
  | SignedPhaseProd :
      ∀ phi x z,
        LowerablePhaseGate (Gate.SignedPhaseProd phi x z)
  | CSignedPhaseProd :
      ∀ ctrl phi x z,
        LowerablePhaseGate (Gate.CSignedPhaseProd ctrl phi x z)
  | zeroExtend :
      ∀ r n,
        LowerablePhaseGate (Gate.zeroExtend r n)
  | signExtend :
      ∀ r n,
        LowerablePhaseGate (Gate.signExtend r n)
  | zeroDealloc :
      ∀ r n,
        LowerablePhaseGate (Gate.zeroDealloc r n)
  | signDealloc :
      ∀ r n,
        LowerablePhaseGate (Gate.signDealloc r n)
  | RadixReverse :
      ∀ r m,
        LowerablePhaseGate (Gate.RadixReverse r m)

end Shor


namespace Shor
open Gate
open Operations

/-! =========================================================
    Interpreter Simp Rules
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
    Lowerable-Gate Facts
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

end LowerablePhaseGate

/-! =========================================================
    Lowerability Of Compiled Signed Operation Lists
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

end Shor
