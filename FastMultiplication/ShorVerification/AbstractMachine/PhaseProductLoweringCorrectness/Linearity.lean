import FastMultiplication.ShorVerification.AbstractMachine.PhaseProductLoweringCorrectness.PlanSemantics

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
    [LowerGateClass qs]
    [GateSemanticsFacts qs]
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
  induction plan with
  | id initSize =>
      change
        LowerGateClass.evalL
            (qs := qs)
            LowGate.id
            0
          =
        0
      exact LowerGateClass.evalL_id (qs := qs) 0
  | seq left right ihLeft ihRight =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.seq
              (lowerGateRec left)
              (lowerGateRec right))
            0
          =
        0
      rw [
        LowerGateClass.evalL_seq,
        ihLeft,
        ihRight
      ]
  | H initSize qbit =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.H qbit)
            0
          =
        0
      rw [
        LowerGateClass.evalL_H,
        qs.eval_zero
      ]
  | X initSize qbit =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.X qbit)
            0
          =
        0
      rw [
        LowerGateClass.evalL_X,
        qs.eval_zero
      ]
  | Prim initSize tag args =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.Prim tag args)
            0
          =
        0
      rw [
        LowerGateClass.evalL_Prim,
        qs.eval_zero
      ]
  | ShiftL initSize r n =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.ShiftL r n)
            0
          =
        0
      rw [
        LowerGateClass.evalL_shiftL,
        qs.eval_zero
      ]
  | ShiftR initSize r n =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.ShiftR r n)
            0
          =
        0
      rw [
        LowerGateClass.evalL_shiftR,
        qs.eval_zero
      ]
  | Negate initSize r =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.Negate r)
            0
          =
        0
      rw [
        LowerGateClass.evalL_negate,
        qs.eval_zero
      ]
  | AddScaled initSize dst src negSrc shift =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.AddScaled dst src negSrc shift)
            0
          =
        0
      rw [
        LowerGateClass.evalL_addScaled,
        qs.eval_zero
      ]
  | zeroExtend initSize r n =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.zeroExtend r n)
            0
          =
        0
      rw [
        LowerGateClass.evalL_zeroExtend,
        qs.eval_zero
      ]
  | signExtend initSize r n =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.signExtend r n)
            0
          =
        0
      rw [
        LowerGateClass.evalL_signExtend,
        qs.eval_zero
      ]
  | zeroDealloc initSize r n =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.zeroDealloc r n)
            0
          =
        0
      rw [
        LowerGateClass.evalL_zeroDealloc,
        qs.eval_zero
      ]
  | signDealloc initSize r n =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.signDealloc r n)
            0
          =
        0
      rw [
        LowerGateClass.evalL_signDealloc,
        qs.eval_zero
      ]
  | RadixReverse initSize r m =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.RadixReverse r m)
            0
          =
        0
      rw [
        LowerGateClass.evalL_radixReverse,
        qs.eval_zero
      ]
  | signedBase phi x z hstop =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.Naive_SignedPhaseProd phi x z)
            0
          =
        0
      rw [
        LowerGateClass.evalL_naive_signedPhaseProd,
        qs.eval_zero
      ]
  | signedStep phi x z layout hrec hcapacity child ihChild =>
      exact ihChild
  | cSignedBase ctrl phi x z hstop =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.Naive_CSignedPhaseProd
              ctrl phi x z)
            0
          =
        0
      rw [
        LowerGateClass.evalL_naive_csignedPhaseProd,
        qs.eval_zero
      ]
  | cSignedStep
      ctrl phi x z layout
      hrec hcapacity hctrl child ihChild =>
      exact ihChild

/-- Readiness is closed under the zero state. -/
lemma PhaseLoweringReady.zero
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
  induction plan generalizing ψ φ with
  | id initSize =>
      change
        LowerGateClass.evalL
            (qs := qs)
            LowGate.id
            (ψ + φ)
          =
        LowerGateClass.evalL
            (qs := qs)
            LowGate.id
            ψ
          +
        LowerGateClass.evalL
            (qs := qs)
            LowGate.id
            φ
      simp only [LowerGateClass.evalL_id]
  | seq left right ihLeft ihRight =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.seq
              (lowerGateRec left)
              (lowerGateRec right))
            (ψ + φ)
          =
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.seq
              (lowerGateRec left)
              (lowerGateRec right))
            ψ
          +
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.seq
              (lowerGateRec left)
              (lowerGateRec right))
            φ
      rw [LowerGateClass.evalL_seq]
      rw [ihLeft]
      rw [ihRight]
      rw [
        LowerGateClass.evalL_seq,
        LowerGateClass.evalL_seq
      ]
  | H initSize qbit =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.H qbit)
            (ψ + φ)
          =
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.H qbit)
            ψ
          +
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.H qbit)
            φ
      simpa only [LowerGateClass.evalL_H] using
        qs.eval_add (Gate.H qbit) ψ φ
  | X initSize qbit =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.X qbit)
            (ψ + φ)
          =
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.X qbit)
            ψ
          +
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.X qbit)
            φ
      simpa only [LowerGateClass.evalL_X] using
        qs.eval_add (Gate.X qbit) ψ φ
  | Prim initSize tag args =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.Prim tag args)
            (ψ + φ)
          =
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.Prim tag args)
            ψ
          +
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.Prim tag args)
            φ
      simpa only [LowerGateClass.evalL_Prim] using
        qs.eval_add (Gate.Prim tag args) ψ φ
  | ShiftL initSize r n =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.ShiftL r n)
            (ψ + φ)
          =
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.ShiftL r n)
            ψ
          +
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.ShiftL r n)
            φ
      simpa only [LowerGateClass.evalL_shiftL] using
        qs.eval_add (Gate.ShiftL r n) ψ φ
  | ShiftR initSize r n =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.ShiftR r n)
            (ψ + φ)
          =
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.ShiftR r n)
            ψ
          +
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.ShiftR r n)
            φ
      simpa only [LowerGateClass.evalL_shiftR] using
        qs.eval_add (Gate.ShiftR r n) ψ φ
  | Negate initSize r =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.Negate r)
            (ψ + φ)
          =
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.Negate r)
            ψ
          +
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.Negate r)
            φ
      simpa only [LowerGateClass.evalL_negate] using
        qs.eval_add (Gate.Negate r) ψ φ
  | AddScaled initSize dst src negSrc shift =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.AddScaled dst src negSrc shift)
            (ψ + φ)
          =
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.AddScaled dst src negSrc shift)
            ψ
          +
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.AddScaled dst src negSrc shift)
            φ
      simpa only [LowerGateClass.evalL_addScaled] using
        qs.eval_add
          (Gate.AddScaled dst src negSrc shift)
          ψ φ
  | zeroExtend initSize r n =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.zeroExtend r n)
            (ψ + φ)
          =
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.zeroExtend r n)
            ψ
          +
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.zeroExtend r n)
            φ
      simpa only [LowerGateClass.evalL_zeroExtend] using
        qs.eval_add (Gate.zeroExtend r n) ψ φ
  | signExtend initSize r n =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.signExtend r n)
            (ψ + φ)
          =
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.signExtend r n)
            ψ
          +
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.signExtend r n)
            φ
      simpa only [LowerGateClass.evalL_signExtend] using
        qs.eval_add (Gate.signExtend r n) ψ φ
  | zeroDealloc initSize r n =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.zeroDealloc r n)
            (ψ + φ)
          =
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.zeroDealloc r n)
            ψ
          +
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.zeroDealloc r n)
            φ
      simpa only [LowerGateClass.evalL_zeroDealloc] using
        qs.eval_add (Gate.zeroDealloc r n) ψ φ
  | signDealloc initSize r n =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.signDealloc r n)
            (ψ + φ)
          =
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.signDealloc r n)
            ψ
          +
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.signDealloc r n)
            φ
      simpa only [LowerGateClass.evalL_signDealloc] using
        qs.eval_add (Gate.signDealloc r n) ψ φ
  | RadixReverse initSize r m =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.RadixReverse r m)
            (ψ + φ)
          =
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.RadixReverse r m)
            ψ
          +
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.RadixReverse r m)
            φ
      simpa only [LowerGateClass.evalL_radixReverse] using
        qs.eval_add (Gate.RadixReverse r m) ψ φ
  | signedBase phase x z hstop =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.Naive_SignedPhaseProd phase x z)
            (ψ + φ)
          =
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.Naive_SignedPhaseProd phase x z)
            ψ
          +
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.Naive_SignedPhaseProd phase x z)
            φ
      simpa only [
        LowerGateClass.evalL_naive_signedPhaseProd
      ] using
        qs.eval_add
          (Gate.SignedPhaseProd phase x z)
          ψ φ
  | signedStep phase x z layout hrec hcapacity child ihChild =>
      exact ihChild ψ φ
  | cSignedBase ctrl phase x z hstop =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.Naive_CSignedPhaseProd ctrl phase x z)
            (ψ + φ)
          =
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.Naive_CSignedPhaseProd ctrl phase x z)
            ψ
          +
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.Naive_CSignedPhaseProd ctrl phase x z)
            φ
      simpa only [
        LowerGateClass.evalL_naive_csignedPhaseProd
      ] using
        qs.eval_add
          (Gate.CSignedPhaseProd ctrl phase x z)
          ψ φ
  | cSignedStep
      ctrl phase x z layout
      hrec hcapacity hctrl child ihChild =>
      exact ihChild ψ φ

/-- Readiness is closed under addition of states. -/
lemma PhaseLoweringReady.add
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
  induction plan generalizing ψ with
  | id initSize =>
      change
        LowerGateClass.evalL
            (qs := qs)
            LowGate.id
            (a • ψ)
          =
        a •
          LowerGateClass.evalL
            (qs := qs)
            LowGate.id
            ψ
      simp only [LowerGateClass.evalL_id]
  | seq left right ihLeft ihRight =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.seq
              (lowerGateRec left)
              (lowerGateRec right))
            (a • ψ)
          =
        a •
          LowerGateClass.evalL
            (qs := qs)
            (LowGate.seq
              (lowerGateRec left)
              (lowerGateRec right))
            ψ
      rw [LowerGateClass.evalL_seq]
      rw [ihLeft]
      rw [ihRight]
      rw [LowerGateClass.evalL_seq]
  | H initSize qbit =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.H qbit)
            (a • ψ)
          =
        a •
          LowerGateClass.evalL
            (qs := qs)
            (LowGate.H qbit)
            ψ
      simpa only [LowerGateClass.evalL_H] using
        qs.eval_smul (Gate.H qbit) a ψ
  | X initSize qbit =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.X qbit)
            (a • ψ)
          =
        a •
          LowerGateClass.evalL
            (qs := qs)
            (LowGate.X qbit)
            ψ
      simpa only [LowerGateClass.evalL_X] using
        qs.eval_smul (Gate.X qbit) a ψ
  | Prim initSize tag args =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.Prim tag args)
            (a • ψ)
          =
        a •
          LowerGateClass.evalL
            (qs := qs)
            (LowGate.Prim tag args)
            ψ
      simpa only [LowerGateClass.evalL_Prim] using
        qs.eval_smul (Gate.Prim tag args) a ψ
  | ShiftL initSize r n =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.ShiftL r n)
            (a • ψ)
          =
        a •
          LowerGateClass.evalL
            (qs := qs)
            (LowGate.ShiftL r n)
            ψ
      simpa only [LowerGateClass.evalL_shiftL] using
        qs.eval_smul (Gate.ShiftL r n) a ψ
  | ShiftR initSize r n =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.ShiftR r n)
            (a • ψ)
          =
        a •
          LowerGateClass.evalL
            (qs := qs)
            (LowGate.ShiftR r n)
            ψ
      simpa only [LowerGateClass.evalL_shiftR] using
        qs.eval_smul (Gate.ShiftR r n) a ψ
  | Negate initSize r =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.Negate r)
            (a • ψ)
          =
        a •
          LowerGateClass.evalL
            (qs := qs)
            (LowGate.Negate r)
            ψ
      simpa only [LowerGateClass.evalL_negate] using
        qs.eval_smul (Gate.Negate r) a ψ
  | AddScaled initSize dst src negSrc shift =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.AddScaled dst src negSrc shift)
            (a • ψ)
          =
        a •
          LowerGateClass.evalL
            (qs := qs)
            (LowGate.AddScaled dst src negSrc shift)
            ψ
      simpa only [LowerGateClass.evalL_addScaled] using
        qs.eval_smul
          (Gate.AddScaled dst src negSrc shift)
          a ψ
  | zeroExtend initSize r n =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.zeroExtend r n)
            (a • ψ)
          =
        a •
          LowerGateClass.evalL
            (qs := qs)
            (LowGate.zeroExtend r n)
            ψ
      simpa only [LowerGateClass.evalL_zeroExtend] using
        qs.eval_smul (Gate.zeroExtend r n) a ψ
  | signExtend initSize r n =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.signExtend r n)
            (a • ψ)
          =
        a •
          LowerGateClass.evalL
            (qs := qs)
            (LowGate.signExtend r n)
            ψ
      simpa only [LowerGateClass.evalL_signExtend] using
        qs.eval_smul (Gate.signExtend r n) a ψ
  | zeroDealloc initSize r n =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.zeroDealloc r n)
            (a • ψ)
          =
        a •
          LowerGateClass.evalL
            (qs := qs)
            (LowGate.zeroDealloc r n)
            ψ
      simpa only [LowerGateClass.evalL_zeroDealloc] using
        qs.eval_smul (Gate.zeroDealloc r n) a ψ
  | signDealloc initSize r n =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.signDealloc r n)
            (a • ψ)
          =
        a •
          LowerGateClass.evalL
            (qs := qs)
            (LowGate.signDealloc r n)
            ψ
      simpa only [LowerGateClass.evalL_signDealloc] using
        qs.eval_smul (Gate.signDealloc r n) a ψ
  | RadixReverse initSize r m =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.RadixReverse r m)
            (a • ψ)
          =
        a •
          LowerGateClass.evalL
            (qs := qs)
            (LowGate.RadixReverse r m)
            ψ
      simpa only [LowerGateClass.evalL_radixReverse] using
        qs.eval_smul (Gate.RadixReverse r m) a ψ
  | signedBase phase x z hstop =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.Naive_SignedPhaseProd phase x z)
            (a • ψ)
          =
        a •
          LowerGateClass.evalL
            (qs := qs)
            (LowGate.Naive_SignedPhaseProd phase x z)
            ψ
      simpa only [
        LowerGateClass.evalL_naive_signedPhaseProd
      ] using
        qs.eval_smul
          (Gate.SignedPhaseProd phase x z)
          a ψ
  | signedStep phase x z layout hrec hcapacity child ihChild =>
      exact ihChild ψ
  | cSignedBase ctrl phase x z hstop =>
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.Naive_CSignedPhaseProd ctrl phase x z)
            (a • ψ)
          =
        a •
          LowerGateClass.evalL
            (qs := qs)
            (LowGate.Naive_CSignedPhaseProd ctrl phase x z)
            ψ
      simpa only [
        LowerGateClass.evalL_naive_csignedPhaseProd
      ] using
        qs.eval_smul
          (Gate.CSignedPhaseProd ctrl phase x z)
          a ψ
  | cSignedStep
      ctrl phase x z layout
      hrec hcapacity hctrl child ihChild =>
      exact ihChild ψ

/-- Readiness is closed under scalar multiplication. -/
lemma PhaseLoweringReady.smul
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
