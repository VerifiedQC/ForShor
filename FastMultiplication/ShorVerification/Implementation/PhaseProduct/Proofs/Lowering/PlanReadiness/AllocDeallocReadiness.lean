import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Lowering.PlanReadiness.BodyReadiness

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
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    {initSize : ℕ}
    {U V : Gate}
    (h : V = U)
    (plan : PhaseLoweringPlan k hk pts hpts ops initSize U)
    {ψ : qs.State}
    (hready : PhaseLoweringReady qs plan ψ) :
    PhaseLoweringReady qs
      (Eq.mpr (congrArg (PhaseLoweringPlan k hk pts hpts ops initSize) h) plan) ψ := by
  subst V
  exact hready

/-- Allocation chunk plans are always ready because they contain only primitive low gates. -/
lemma planAllocChunkGate_ready
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    (initSize : ℕ)
    (i : Fin k)
    (src dst : ExtReg)
    (ψ : qs.State) :
    PhaseLoweringReady qs
      (planAllocChunkGate (hk := hk) (pts := pts) (hpts := hpts) (ops := ops) initSize i src dst)
      ψ := by
  by_cases hzero : extraDelta src dst = 0
  · have hdecZero : instDecidableEqNat (extraDelta src dst) 0 = Decidable.isTrue hzero :=
      Subsingleton.elim _ _
    unfold planAllocChunkGate
    simp only [hdecZero]
    dsimp only [_root_.id]
    apply PhaseLoweringReady.cast_gate_mpr
    all_goals
      simp [allocChunkGate, hzero, PhaseLoweringReady]
  · by_cases htop : isTopChunk i
    · have hdecZero : instDecidableEqNat (extraDelta src dst) 0 = Decidable.isFalse hzero :=
        Subsingleton.elim _ _
      have hdecTop : instDecidableIsTopChunk i = Decidable.isTrue htop := Subsingleton.elim _ _
      unfold planAllocChunkGate
      simp only [hdecZero, hdecTop]
      dsimp only [_root_.id]
      apply PhaseLoweringReady.cast_gate_mpr
      all_goals
        first
        | apply PhaseLoweringReady.cast_gate_mpr
        | simp [allocChunkGate, hzero, htop]
      all_goals
        simp [htop, PhaseLoweringReady]
    · have hdecZero : instDecidableEqNat (extraDelta src dst) 0 = Decidable.isFalse hzero :=
        Subsingleton.elim _ _
      have hdecTop : instDecidableIsTopChunk i = Decidable.isFalse htop := Subsingleton.elim _ _
      unfold planAllocChunkGate
      simp only [hdecZero, hdecTop]
      dsimp only [_root_.id]
      apply PhaseLoweringReady.cast_gate_mpr
      all_goals
        first
        | apply PhaseLoweringReady.cast_gate_mpr
        | simp [allocChunkGate, hzero, htop]
      all_goals
        simp [htop, PhaseLoweringReady]

/-- Auxiliary allocation plans are ready for every starting state. -/
lemma planCompileSignedAllocationsAux_ready
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    (initSize : ℕ)
    (src dst : LayoutState k) :
    ∀ n hn ψ,
      PhaseLoweringReady qs
        (planCompileSignedAllocationsAux (hk := hk) (pts := pts) (hpts := hpts) (ops := ops)
          initSize src dst n hn)
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
    {k : ℕ}
    (hk : 1 < k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (ops : Prog k)
    (initSize : ℕ)
    (src dst : LayoutState k)
    (ψ : qs.State) :
    PhaseLoweringReady qs
      (planCompileSignedAllocations (hk := hk) (pts := pts) (hpts := hpts) (ops := ops)
        initSize src dst)
      ψ := by
  unfold planCompileSignedAllocations
  exact planCompileSignedAllocationsAux_ready qs initSize src dst k le_rfl ψ

/-- Deallocation chunk plans are always ready because they contain only primitive low gates. -/
lemma planDeallocChunkGate_ready
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    (initSize : ℕ)
    (i : Fin k)
    (src dst : ExtReg)
    (ψ : qs.State) :
    PhaseLoweringReady qs
      (planDeallocChunkGate (hk := hk) (pts := pts) (hpts := hpts) (ops := ops) initSize i src dst)
      ψ := by
  by_cases hzero : extraDelta src dst = 0
  · have hdecZero : instDecidableEqNat (extraDelta src dst) 0 = Decidable.isTrue hzero :=
      Subsingleton.elim _ _
    unfold planDeallocChunkGate
    simp only [hdecZero]
    dsimp only [_root_.id]
    apply PhaseLoweringReady.cast_gate_mpr
    all_goals
      simp [deallocChunkGate, hzero, PhaseLoweringReady]
  · by_cases htop : isTopChunk i
    · have hdecZero : instDecidableEqNat (extraDelta src dst) 0 = Decidable.isFalse hzero :=
        Subsingleton.elim _ _
      have hdecTop : instDecidableIsTopChunk i = Decidable.isTrue htop := Subsingleton.elim _ _
      unfold planDeallocChunkGate
      simp only [hdecZero, hdecTop]
      dsimp only [_root_.id]
      apply PhaseLoweringReady.cast_gate_mpr
      all_goals
        first
        | apply PhaseLoweringReady.cast_gate_mpr
        | simp [deallocChunkGate, hzero, htop]
      all_goals
        simp [htop, PhaseLoweringReady]
    · have hdecZero : instDecidableEqNat (extraDelta src dst) 0 = Decidable.isFalse hzero :=
        Subsingleton.elim _ _
      have hdecTop : instDecidableIsTopChunk i = Decidable.isFalse htop := Subsingleton.elim _ _
      unfold planDeallocChunkGate
      simp only [hdecZero, hdecTop]
      dsimp only [_root_.id]
      apply PhaseLoweringReady.cast_gate_mpr
      all_goals
        first
        | apply PhaseLoweringReady.cast_gate_mpr
        | simp [deallocChunkGate, hzero, htop]
      all_goals
        simp [htop, PhaseLoweringReady]

/-- Auxiliary deallocation plans are ready for every starting state. -/
lemma planCompileSignedDeallocationsAux_ready
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    (initSize : ℕ)
    (src dst : LayoutState k) :
    ∀ n hn ψ,
      PhaseLoweringReady qs
        (planCompileSignedDeallocationsAux (hk := hk) (pts := pts) (hpts := hpts) (ops := ops)
          initSize src dst n hn)
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
    {k : ℕ}
    (hk : 1 < k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (ops : Prog k)
    (initSize : ℕ)
    (src dst : LayoutState k)
    (ψ : qs.State) :
    PhaseLoweringReady qs
      (planCompileSignedDeallocations (hk := hk) (pts := pts) (hpts := hpts) (ops := ops)
        initSize src dst)
      ψ := by
  unfold planCompileSignedDeallocations
  exact planCompileSignedDeallocationsAux_ready qs initSize src dst k le_rfl ψ

end Shor
