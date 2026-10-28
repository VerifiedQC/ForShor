import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering.PlanReadiness.BodyReadiness

namespace Shor
open Gate
open Operations

/-! =========================================================
    Allocation And Deallocation Readiness

    Allocation and deallocation chunks compile to primitive low gates, so their
    readiness proofs mostly transport across definitional equalities exposed by
    the plan constructors.
========================================================= -/

/-- Transport readiness across an equality of high-level gates in a plan type. -/
lemma PhaseLoweringReady.cast_gate_mpr
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    {P : ShorLoweringPolicy}
    {initSize : ℕ}
    {U V : Gate}
    (h : V = U)
    (plan : PhaseLoweringPlan P initSize U)
    {ψ : qs.State}
    (hready : PhaseLoweringReady qs plan ψ) :
    PhaseLoweringReady qs
      (Eq.mpr (congrArg (PhaseLoweringPlan P initSize) h) plan) ψ := by
  subst V
  exact hready

/-- Readiness survives the index cast the dispatcher performs on a child plan.

The planner builds the child at the child's own `phaseInputSize` and transports
it along `childInputSize` to the parent's `nextSignedWidth`; this is the lemma
that carries readiness across that transport. -/
lemma PhaseLoweringReady.cast_initSize
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    {P : ShorLoweringPolicy}
    {m n : ℕ}
    (h : m = n)
    {U : Gate}
    (plan : PhaseLoweringPlan P m U)
    {ψ : qs.State}
    (hready : PhaseLoweringReady qs plan ψ) :
    PhaseLoweringReady qs (h ▸ plan : PhaseLoweringPlan P n U) ψ := by
  subst h
  exact hready

/-- Readiness of a dependent `if` between two plans of one type follows from readiness of
both branches. The `Decidable` instance is an ordinary implicit argument so that it unifies
with whichever instance the plan was built with. -/
lemma PhaseLoweringReady.dite
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    {P : ShorLoweringPolicy}
    {initSize : ℕ}
    {U : Gate}
    {c : Prop}
    {inst : Decidable c}
    {t : c → PhaseLoweringPlan P initSize U}
    {e : ¬c → PhaseLoweringPlan P initSize U}
    {ψ : qs.State}
    (ht : ∀ h, PhaseLoweringReady qs (t h) ψ)
    (he : ∀ h, PhaseLoweringReady qs (e h) ψ) :
    PhaseLoweringReady qs (@dite _ c inst t e) ψ := by
  by_cases h : c
  · rw [dite_eq_left h]; exact ht h
  · rw [dite_eq_right h]; exact he h

/-- Allocation chunk plans are always ready because they contain only primitive low gates. -/
lemma planAllocChunkGate_ready
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    {P : ShorLoweringPolicy}
    {k : ℕ}
    (initSize : ℕ)
    (i : Fin k)
    (src dst : ExtReg)
    (ψ : qs.State) :
    PhaseLoweringReady qs
      (planAllocChunkGate (P := P) initSize i src dst)
      ψ := by
  unfold planAllocChunkGate
  try dsimp only [_root_.id]
  apply PhaseLoweringReady.dite
  · intro hzero
    apply PhaseLoweringReady.cast_gate_mpr
    all_goals simp [allocChunkGate, hzero, PhaseLoweringReady]
  · intro hzero
    apply PhaseLoweringReady.cast_gate_mpr
    case hready =>
      apply PhaseLoweringReady.dite
      · intro htop
        apply PhaseLoweringReady.cast_gate_mpr
        all_goals simp [htop, PhaseLoweringReady]
      · intro htop
        apply PhaseLoweringReady.cast_gate_mpr
        all_goals simp [htop, PhaseLoweringReady]
    all_goals simp [allocChunkGate, hzero]

/-- Auxiliary allocation plans are ready for every starting state. -/
lemma planCompileSignedAllocationsAux_ready
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    {P : ShorLoweringPolicy}
    {k : ℕ}
    (initSize : ℕ)
    (src dst : LayoutState k) :
    ∀ n hn ψ,
      PhaseLoweringReady qs
        (planCompileSignedAllocationsAux (P := P) initSize src dst n hn)
        ψ := by
  intro n
  induction n with
  | zero =>
      intro hn ψ
      trivial
  | succ n ih =>
      intro hn ψ
      dsimp only [planCompileSignedAllocationsAux]
      refine ⟨?_, ?_, ?_⟩
      · exact ih _ _
      · apply planAllocChunkGate_ready
      · apply planAllocChunkGate_ready

/-- Full signed-allocation plans are ready for every starting state. -/
lemma planCompileSignedAllocations_ready
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    {P : ShorLoweringPolicy}
    {k : ℕ}
    (initSize : ℕ)
    (src dst : LayoutState k)
    (ψ : qs.State) :
    PhaseLoweringReady qs
      (planCompileSignedAllocations (P := P) initSize src dst)
      ψ := by
  unfold planCompileSignedAllocations
  exact planCompileSignedAllocationsAux_ready (P := P) qs initSize src dst k le_rfl ψ

/-- Deallocation chunk plans are always ready because they contain only primitive low gates. -/
lemma planDeallocChunkGate_ready
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    {P : ShorLoweringPolicy}
    {k : ℕ}
    (initSize : ℕ)
    (i : Fin k)
    (src dst : ExtReg)
    (ψ : qs.State) :
    PhaseLoweringReady qs
      (planDeallocChunkGate (P := P) initSize i src dst)
      ψ := by
  unfold planDeallocChunkGate
  try dsimp only [_root_.id]
  apply PhaseLoweringReady.dite
  · intro hzero
    apply PhaseLoweringReady.cast_gate_mpr
    all_goals simp [deallocChunkGate, hzero, PhaseLoweringReady]
  · intro hzero
    apply PhaseLoweringReady.cast_gate_mpr
    case hready =>
      apply PhaseLoweringReady.dite
      · intro htop
        apply PhaseLoweringReady.cast_gate_mpr
        all_goals simp [htop, PhaseLoweringReady]
      · intro htop
        apply PhaseLoweringReady.cast_gate_mpr
        all_goals simp [htop, PhaseLoweringReady]
    all_goals simp [deallocChunkGate, hzero]

/-- Auxiliary deallocation plans are ready for every starting state. -/
lemma planCompileSignedDeallocationsAux_ready
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    {P : ShorLoweringPolicy}
    {k : ℕ}
    (initSize : ℕ)
    (src dst : LayoutState k) :
    ∀ n hn ψ,
      PhaseLoweringReady qs
        (planCompileSignedDeallocationsAux (P := P) initSize src dst n hn)
        ψ := by
  intro n
  induction n with
  | zero =>
      intro hn ψ
      trivial
  | succ n ih =>
      intro hn ψ
      dsimp only [planCompileSignedDeallocationsAux]
      refine ⟨?_, ?_, ?_⟩
      · apply planDeallocChunkGate_ready
      · apply planDeallocChunkGate_ready
      · exact ih _ _

/-- Full signed-deallocation plans are ready for every starting state. -/
lemma planCompileSignedDeallocations_ready
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    {P : ShorLoweringPolicy}
    {k : ℕ}
    (initSize : ℕ)
    (src dst : LayoutState k)
    (ψ : qs.State) :
    PhaseLoweringReady qs
      (planCompileSignedDeallocations (P := P) initSize src dst)
      ψ := by
  unfold planCompileSignedDeallocations
  exact planCompileSignedDeallocationsAux_ready (P := P) qs initSize src dst k le_rfl ψ

end Shor
