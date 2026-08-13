import FastMultiplication.ShorVerification.Implementation.PhaseProduct.LoweringCorrectness.PlanSemantics

namespace Shor
open Gate
open Operations

/-!
# Phase-Product Lowering Linearity
This file contains the semantic closure lemmas used to lift basis-level
readiness and cleanliness proofs to arbitrary quantum states. It proves that
phase products preserve clean recursive workspace and that recursive-plan
evaluation and readiness respect zero, addition, and scalar multiplication.
-/

/-! =========================================================
    Section 1: Cleanliness preservation and linear closure
    Phase products act by phases on basis states, so they preserve recursive
    workspace-clean predicates. The rest of this file shows that low-level
    evaluation and readiness are closed under the vector-space operations used
    by the quantum semantics.
========================================================= -/

/-- A signed phase product preserves recursive workspace cleanliness. -/
lemma eval_SignedPhaseProd_preserves_recursiveWorkspaceClean
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (phi : ℝ)
    (x z : ExtReg)
    {ψ : qs.State}
    (hclean :
      RecursiveWorkspaceCleanState
        qs x z ψ) :
    RecursiveWorkspaceCleanState
      qs x z
      (qs.eval
        (Gate.SignedPhaseProd phi x z)
        ψ) := by
  induction hclean with
  | zero =>
      rw [qs.eval_zero]
      exact CleanClosure.zero
  | ket b hcleanBasis =>
      rw [PhaseSemantics.eval_SignedPhaseProd_ket]
      exact
        CleanClosure.smul
          _
          (CleanClosure.ket
            b
            hcleanBasis)
  | add hψ hφ ihψ ihφ =>
      rw [qs.eval_add]
      exact
        CleanClosure.add
          ihψ
          ihφ
  | smul a hψ ihψ =>
      rw [qs.eval_smul]
      exact
        CleanClosure.smul
          a
          ihψ
/-- A basis state has zeroes in every reserve bit owned by a layout. -/
def LayoutReserveCleanBasis
    {Basis : Type u}
    [RegEncoding Basis]
    {k : ℕ}
    (st : LayoutState k)
    (b : Basis) :
    Prop :=
  (∀ i : Fin k,
    ExtReg.FreshFor
      (st.xslot i)
      (st.xslot i).capacity
      b)
  ∧
  (∀ i : Fin k,
    ExtReg.FreshFor
      (st.zslot i)
      (st.zslot i).capacity
      b)

/-- State-level reserve cleanliness, generated from clean basis states and linear closure. -/
abbrev LayoutReserveCleanState
    (qs : QSemantics) [RegEncoding qs.Basis] {k : ℕ} (st : LayoutState k) : qs.State → Prop :=
  CleanClosure (fun b => LayoutReserveCleanBasis st b)

/-- A ready standard plan preserves recursive workspace cleanliness after low-level evaluation. -/
lemma standardSignedPhaseLoweringPlan_preserves_clean_of_ready
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    (k : ℕ)
    (hk : 1 < k)
    (phi : ℝ)
    (x z : ExtReg)
    (ops : Prog k)
    (ψ : qs.State)
    (hstatic :
      SignedRecursiveWorkspaceOK ops x z)
    (hclean :
      RecursiveWorkspaceCleanState qs x z ψ)
    (hready :
      PhaseLoweringReady
        qs
        (standardSignedPhaseLoweringPlan
          k hk phi x z ops hstatic)
        ψ)
    (hC :
      ProgConsumesPtsSafe
        (k := k)
        (by omega)
        State.start_state
        ops
        (genInterpolationPoints k))
    (hRun :
      run? ops State.start_state =
        some State.start_state) :
    RecursiveWorkspaceCleanState
      qs x z
      (LowerGateClass.evalL
        (qs := qs)
        (lowerGateRec
          (standardSignedPhaseLoweringPlan
            k hk phi x z ops hstatic))
        ψ) := by
  have hInterp :
      GoodToomCookPoints
        k
        (genInterpolationPoints k)
        (generatedInterpolationPoints_length k) := by
    simpa using
      genInterpolationPoints_good k
  have heval :
      LowerGateClass.evalL
          (qs := qs)
          (lowerGateRec
            (standardSignedPhaseLoweringPlan
              k hk phi x z ops hstatic))
          ψ
        =
      qs.eval
          (Gate.SignedPhaseProd phi x z)
          ψ := by
    exact
      evalL_lowerGateRec_correct
        (qs := qs)
        (hInterp := hInterp)
        (hC := hC)
        (hRun := hRun)
        (standardSignedPhaseLoweringPlan
          k hk phi x z ops hstatic)
        ψ
        hready
  rw [heval]
  exact
    eval_SignedPhaseProd_preserves_recursiveWorkspaceClean
      qs phi x z hclean

/-- Low-level evaluation of a recursive plan maps the zero state to zero. -/
lemma evalL_lowerGateRec_zero
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    {initSize : ℕ}
    {U : Gate}
    (plan :
      PhaseLoweringPlan
        k hk pts hpts ops initSize U) :
    LowerGateClass.evalL
        (qs := qs)
        (lowerGateRec plan)
        0
      =
    0 := by
  exact LowerGateClass.evalL_zero (qs := qs) (lowerGateRec plan)

/-- Readiness is closed under the zero state. -/
lemma PhaseLoweringReady.zero
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [LowerGateClass qs]
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    {initSize : ℕ}
    {U : Gate}
    (plan :
      PhaseLoweringPlan
        k hk pts hpts ops initSize U) :
    PhaseLoweringReady qs plan 0 := by
  induction plan with
  | id initSize =>
      trivial
  | seq left right ihLeft ihRight =>
      change
        PhaseLoweringReady qs left 0
          ∧
        PhaseLoweringReady
          qs
          right
          (LowerGateClass.evalL
            (qs := qs)
            (lowerGateRec left)
            0)
      constructor
      · exact ihLeft
      · rw [evalL_lowerGateRec_zero]
        exact ihRight
  | H initSize qbit =>
      trivial
  | X initSize qbit =>
      trivial
  | Prim initSize tag args =>
      trivial
  | ShiftL initSize r n =>
      trivial
  | ShiftR initSize r n =>
      trivial
  | Negate initSize r =>
      trivial
  | AddScaled initSize dst src negSrc shift =>
      trivial
  | zeroExtend initSize r n =>
      trivial
  | signExtend initSize r n =>
      trivial
  | zeroDealloc initSize r n =>
      trivial
  | signDealloc initSize r n =>
      trivial
  | RadixReverse initSize r m =>
      trivial
  | signedBase phi x z hstop =>
      trivial
  | signedStep
      phi x z layout hrec hcapacity child ihChild =>
      change
        CleanWorkspaceState
            qs
            (initSignedLayoutState layout)
            (scanNeededWidths x z ops)
            0
          ∧
        PhaseLoweringReady qs child 0
      exact
        ⟨CleanClosure.zero, ihChild⟩
  | cSignedBase ctrl phi x z hstop =>
      trivial
  | cSignedStep
      ctrl phi x z layout
      hrec hcapacity hctrl child ihChild =>
      change
        CleanWorkspaceState
            qs
            (initSignedLayoutState layout)
            (scanNeededWidths x z ops)
            0
          ∧
        PhaseLoweringReady qs child 0
      exact
        ⟨CleanClosure.zero, ihChild⟩

/-- Low-level evaluation of a recursive plan is additive. -/
lemma evalL_lowerGateRec_add
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    {initSize : ℕ}
    {U : Gate}
    (plan :
      PhaseLoweringPlan
        k hk pts hpts ops initSize U)
    (ψ φ : qs.State) :
    LowerGateClass.evalL
        (qs := qs)
        (lowerGateRec plan)
        (ψ + φ)
      =
    LowerGateClass.evalL
        (qs := qs)
        (lowerGateRec plan)
        ψ
      +
    LowerGateClass.evalL
        (qs := qs)
        (lowerGateRec plan)
        φ := by
  exact LowerGateClass.evalL_add (qs := qs) (lowerGateRec plan) ψ φ

/-- Readiness is closed under addition of states. -/
lemma PhaseLoweringReady.add
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [LowerGateClass qs]
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    {initSize : ℕ}
    {U : Gate}
    (plan :
      PhaseLoweringPlan
        k hk pts hpts ops initSize U)
    {ψ φ : qs.State}
    (hψ : PhaseLoweringReady qs plan ψ)
    (hφ : PhaseLoweringReady qs plan φ) :
    PhaseLoweringReady qs plan (ψ + φ) := by
  induction plan generalizing ψ φ with
  | id initSize =>
      trivial
  | seq left right ihLeft ihRight =>
      change
        PhaseLoweringReady qs left ψ
          ∧
        PhaseLoweringReady
          qs right
          (LowerGateClass.evalL
            (qs := qs)
            (lowerGateRec left)
            ψ)
        at hψ
      change
        PhaseLoweringReady qs left φ
          ∧
        PhaseLoweringReady
          qs right
          (LowerGateClass.evalL
            (qs := qs)
            (lowerGateRec left)
            φ)
        at hφ
      rcases hψ with ⟨hψLeft, hψRight⟩
      rcases hφ with ⟨hφLeft, hφRight⟩
      change
        PhaseLoweringReady qs left (ψ + φ)
          ∧
        PhaseLoweringReady
          qs right
          (LowerGateClass.evalL
            (qs := qs)
            (lowerGateRec left)
            (ψ + φ))
      constructor
      · exact ihLeft hψLeft hφLeft
      · rw [evalL_lowerGateRec_add]
        exact ihRight hψRight hφRight
  | H initSize qbit =>
      trivial
  | X initSize qbit =>
      trivial
  | Prim initSize tag args =>
      trivial
  | ShiftL initSize r n =>
      trivial
  | ShiftR initSize r n =>
      trivial
  | Negate initSize r =>
      trivial
  | AddScaled initSize dst src negSrc shift =>
      trivial
  | zeroExtend initSize r n =>
      trivial
  | signExtend initSize r n =>
      trivial
  | zeroDealloc initSize r n =>
      trivial
  | signDealloc initSize r n =>
      trivial
  | RadixReverse initSize r m =>
      trivial
  | signedBase phase x z hstop =>
      trivial
  | signedStep
      phase x z layout hrec hcapacity child ihChild =>
      change
        CleanWorkspaceState
            qs
            (initSignedLayoutState layout)
            (scanNeededWidths x z ops)
            ψ
          ∧
        PhaseLoweringReady qs child ψ
        at hψ
      change
        CleanWorkspaceState
            qs
            (initSignedLayoutState layout)
            (scanNeededWidths x z ops)
            φ
          ∧
        PhaseLoweringReady qs child φ
        at hφ
      rcases hψ with ⟨hψClean, hψChild⟩
      rcases hφ with ⟨hφClean, hφChild⟩
      change
        CleanWorkspaceState
            qs
            (initSignedLayoutState layout)
            (scanNeededWidths x z ops)
            (ψ + φ)
          ∧
        PhaseLoweringReady qs child (ψ + φ)
      exact
        ⟨
          CleanClosure.add
            hψClean hφClean,
          ihChild hψChild hφChild
        ⟩
  | cSignedBase ctrl phase x z hstop =>
      trivial
  | cSignedStep
      ctrl phase x z layout
      hrec hcapacity hctrl child ihChild =>
      change
        CleanWorkspaceState
            qs
            (initSignedLayoutState layout)
            (scanNeededWidths x z ops)
            ψ
          ∧
        PhaseLoweringReady qs child ψ
        at hψ
      change
        CleanWorkspaceState
            qs
            (initSignedLayoutState layout)
            (scanNeededWidths x z ops)
            φ
          ∧
        PhaseLoweringReady qs child φ
        at hφ
      rcases hψ with ⟨hψClean, hψChild⟩
      rcases hφ with ⟨hφClean, hφChild⟩
      change
        CleanWorkspaceState
            qs
            (initSignedLayoutState layout)
            (scanNeededWidths x z ops)
            (ψ + φ)
          ∧
        PhaseLoweringReady qs child (ψ + φ)
      exact
        ⟨
          CleanClosure.add
            hψClean hφClean,
          ihChild hψChild hφChild
        ⟩

/-- Low-level evaluation of a recursive plan commutes with scalar multiplication. -/
lemma evalL_lowerGateRec_smul
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [LowerGateClass qs]
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    {initSize : ℕ}
    {U : Gate}
    (plan :
      PhaseLoweringPlan
        k hk pts hpts ops initSize U)
    (a : ℂ)
    (ψ : qs.State) :
    LowerGateClass.evalL
        (qs := qs)
        (lowerGateRec plan)
        (a • ψ)
      =
    a •
      LowerGateClass.evalL
        (qs := qs)
        (lowerGateRec plan)
        ψ := by
  exact LowerGateClass.evalL_smul (qs := qs) (lowerGateRec plan) a ψ

/-- Readiness is closed under scalar multiplication. -/
lemma PhaseLoweringReady.smul
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [LowerGateClass qs]
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    {initSize : ℕ}
    {U : Gate}
    (plan :
      PhaseLoweringPlan
        k hk pts hpts ops initSize U)
    (a : ℂ)
    {ψ : qs.State}
    (hψ : PhaseLoweringReady qs plan ψ) :
    PhaseLoweringReady qs plan (a • ψ) := by
  induction plan generalizing ψ with
  | id initSize =>
      trivial
  | seq left right ihLeft ihRight =>
      change
        PhaseLoweringReady qs left ψ
          ∧
        PhaseLoweringReady
          qs right
          (LowerGateClass.evalL
            (qs := qs)
            (lowerGateRec left)
            ψ)
        at hψ
      rcases hψ with ⟨hLeft, hRight⟩
      change
        PhaseLoweringReady qs left (a • ψ)
          ∧
        PhaseLoweringReady
          qs right
          (LowerGateClass.evalL
            (qs := qs)
            (lowerGateRec left)
            (a • ψ))
      constructor
      · exact ihLeft hLeft
      · rw [evalL_lowerGateRec_smul]
        exact ihRight hRight
  | H initSize qbit =>
      trivial
  | X initSize qbit =>
      trivial
  | Prim initSize tag args =>
      trivial
  | ShiftL initSize r n =>
      trivial
  | ShiftR initSize r n =>
      trivial
  | Negate initSize r =>
      trivial
  | AddScaled initSize dst src negSrc shift =>
      trivial
  | zeroExtend initSize r n =>
      trivial
  | signExtend initSize r n =>
      trivial
  | zeroDealloc initSize r n =>
      trivial
  | signDealloc initSize r n =>
      trivial
  | RadixReverse initSize r m =>
      trivial
  | signedBase phase x z hstop =>
      trivial
  | signedStep
      phase x z layout hrec hcapacity child ihChild =>
      change
        CleanWorkspaceState
            qs
            (initSignedLayoutState layout)
            (scanNeededWidths x z ops)
            ψ
          ∧
        PhaseLoweringReady qs child ψ
        at hψ
      rcases hψ with ⟨hClean, hChild⟩
      change
        CleanWorkspaceState
            qs
            (initSignedLayoutState layout)
            (scanNeededWidths x z ops)
            (a • ψ)
          ∧
        PhaseLoweringReady qs child (a • ψ)
      exact
        ⟨
          CleanClosure.smul a hClean,
          ihChild hChild
        ⟩
  | cSignedBase ctrl phase x z hstop =>
      trivial
  | cSignedStep
      ctrl phase x z layout
      hrec hcapacity hctrl child ihChild =>
      change
        CleanWorkspaceState
            qs
            (initSignedLayoutState layout)
            (scanNeededWidths x z ops)
            ψ
          ∧
        PhaseLoweringReady qs child ψ
        at hψ
      rcases hψ with ⟨hClean, hChild⟩
      change
        CleanWorkspaceState
            qs
            (initSignedLayoutState layout)
            (scanNeededWidths x z ops)
            (a • ψ)
          ∧
        PhaseLoweringReady qs child (a • ψ)
      exact
        ⟨
          CleanClosure.smul a hClean,
          ihChild hChild
        ⟩

end Shor
