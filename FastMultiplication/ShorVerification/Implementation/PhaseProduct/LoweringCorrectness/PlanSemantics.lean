import Mathlib.Data.Nat.Bitwise
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.LoweringCorrectness.Plan

namespace Shor
open Gate
open Operations

/-!
# Phase-Product Plan Semantics
This file defines the semantic readiness predicate for lowering plans and proves
the core interpreter theorem: evaluating the low-level circuit selected by a
ready plan agrees with the high-level gate stored in that plan. It also proves
the one-step semantic facts for compiled signed and controlled signed recursive
phase-product nodes.
-/

/-! =========================================================
    Section 1: Readiness predicates
    Lowering plans contain primitive low gates and recursive phase-product calls.
    Primitive gates need no semantic precondition; recursive nodes require a
    clean recursive workspace before the child plan runs and then readiness for
    that child plan.
========================================================= -/

/-- Semantic precondition required to execute a phase-product lowering plan on a state. -/
noncomputable def PhaseLoweringReady
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
    (plan : PhaseLoweringPlan k hk pts hpts ops initSize U) :
    qs.State → Prop := by
  induction plan with
  | id initSize => exact fun _ => True
  | seq left right readyLeft readyRight =>
      exact fun ψ => readyLeft ψ ∧
        readyRight (LowerGateClass.evalL (qs := qs) (lowerGateRec left) ψ)
  | H initSize qbit => exact fun _ => True
  | X initSize qbit => exact fun _ => True
  | Prim initSize tag args => exact fun _ => True
  | ShiftL initSize r n => exact fun _ => True
  | ShiftR initSize r n => exact fun _ => True
  | Negate initSize r => exact fun _ => True
  | AddScaled initSize dst src negSrc shift => exact fun _ => True
  | zeroExtend initSize r n => exact fun _ => True
  | signExtend initSize r n => exact fun _ => True
  | zeroDealloc initSize r n => exact fun _ => True
  | signDealloc initSize r n => exact fun _ => True
  | RadixReverse initSize r m => exact fun _ => True
  | signedBase phi x z hstop => exact fun _ => True
  | signedStep phi x z layout hrec hcapacity child readyChild =>
      exact fun ψ =>
        CleanWorkspaceState qs (initSignedLayoutState layout) (scanNeededWidths x z ops) ψ
          ∧
        readyChild ψ
  | cSignedBase ctrl phi x z hstop => exact fun _ => True
  | cSignedStep
      ctrl phi x z layout
      hrec hcapacity hctrl child readyChild =>
      exact fun ψ =>
        CleanWorkspaceState qs (initSignedLayoutState layout) (scanNeededWidths x z ops) ψ
          ∧
        readyChild ψ

/-! =========================================================
    Section 2: Correctness of one compiled recursive step
    These lemmas identify the low-level interpreter for a single compiled signed
    or controlled signed phase-product plan with the corresponding high-level
    gate.
========================================================= -/

/-- A compiled signed recursive phase-product gate evaluates to its source signed phase product. -/
lemma eval_compiledSignedPhaseGate_correct
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (k : ℕ)
    (hk : 1 < k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (hInterp : GoodToomCookPoints k pts hpts)
    (ops : Prog k)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (hRun : run? ops State.start_state = some State.start_state)
    (phi : ℝ)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (ψ : qs.State)
    (hclean : CleanWorkspaceState qs (initSignedLayoutState layout) (scanNeededWidths x z ops) ψ) :
    qs.eval (compiledSignedPhaseGate k hk pts hpts ops phi x z layout) ψ
      =
    qs.eval (Gate.SignedPhaseProd phi x z) ψ := by
  unfold compiledSignedPhaseGate
  unfold loweringPhaseCoeff
  apply
    eval_compileOpsToSignedGate_correct
      (qs := qs)
      (k := k)
      (hk := hk)
      (phi := phi)
      (x := x)
      (z := z)
      (layout := layout)
      (pts := pts)
      (hpts := hpts)
      (hInterp := hInterp)
      (ψ := ψ)
      (ops := ops)
      (hC := hC)
      (run_ops_start_state := hRun)
  exact hclean

/-- A compiled controlled signed recursive phase-product gate evaluates to its source controlled gate. -/
lemma eval_compiledCSignedPhaseGate_correct
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    (k : ℕ)
    (hk : 1 < k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (hInterp : GoodToomCookPoints k pts hpts)
    (ops : Prog k)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (hRun : run? ops State.start_state = some State.start_state)
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k)
    (hctrl : layout.ControlDisjoint ctrl)
    (ψ : qs.State)
    (hclean : CleanWorkspaceState qs (initSignedLayoutState layout) (scanNeededWidths x z ops) ψ) :
    qs.eval (compiledCSignedPhaseGate k hk pts hpts ops ctrl phi x z layout) ψ
      =
    qs.eval (Gate.CSignedPhaseProd ctrl phi x z) ψ := by
  unfold compiledCSignedPhaseGate
  unfold loweringPhaseCoeff
  apply
    eval_compileOpsToCSignedGate_correct
      (qs := qs)
      (k := k)
      (hk := hk)
      (ctrl := ctrl)
      (phi := phi)
      (x := x)
      (z := z)
      (layout := layout)
      (hctrl := hctrl)
      (pts := pts)
      (hpts := hpts)
      (hInterp := hInterp)
      (ops := ops)
      (hC := hC)
      (hRun := hRun)
      (ψ := ψ)
  exact hclean

/-! =========================================================
    Section 3: Plan-directed interpreter correctness
    The main induction follows the structure of a lowering plan. Each
    constructor is interpreted by the low-level evaluator and compared with the
    high-level gate it implements; recursive nodes use readiness to discharge
    the child call.
========================================================= -/

/-- Correctness of the recursive lowering-plan interpreter under the semantic readiness predicate. -/
lemma evalL_lowerGateRec_correct
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    (hInterp : GoodToomCookPoints k pts hpts)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops pts)
    (hRun : run? ops State.start_state = some State.start_state)
    {initSize : ℕ}
    {U : Gate}
    (plan : PhaseLoweringPlan  k hk pts hpts ops initSize U) :
    ∀ ψ : qs.State,
      PhaseLoweringReady qs plan ψ →
      LowerGateClass.evalL (qs := qs) (lowerGateRec plan) ψ
        =
      qs.eval U ψ := by
  induction plan with
  | id initSize =>
      intro ψ _
      change
        LowerGateClass.evalL
            (qs := qs)
            LowGate.id
            ψ
          =
        qs.eval Gate.id ψ
      calc
        LowerGateClass.evalL
            (qs := qs)
            LowGate.id
            ψ
            = ψ :=
          LowerGateClass.evalL_id
            (qs := qs)
            ψ
        _ = qs.eval Gate.id ψ :=
          (qs.eval_id ψ).symm
  | seq left right ihLeft ihRight =>
      intro ψ hready
      change
        PhaseLoweringReady qs left ψ ∧
        PhaseLoweringReady
          qs
          right
          (LowerGateClass.evalL
            (qs := qs)
            (lowerGateRec left)
            ψ)
        at hready
      rcases hready with ⟨hleft, hright⟩
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.seq
              (lowerGateRec left)
              (lowerGateRec right))
            ψ
          =
        qs.eval _ ψ
      rw [LowerGateClass.evalL_seq]
      rw [ihRight _ hright]
      rw [ihLeft _ hleft]
      exact (qs.eval_seq _ _ ψ).symm
  | H initSize qbit =>
      intro ψ _
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.H qbit)
            ψ
          =
        qs.eval (Gate.H qbit) ψ
      exact
        LowerGateClass.evalL_H
          (qs := qs)
          qbit
          ψ
  | X initSize qbit =>
      intro ψ _
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.X qbit)
            ψ
          =
        qs.eval (Gate.X qbit) ψ
      exact
        LowerGateClass.evalL_X
          (qs := qs)
          qbit
          ψ
  | Prim initSize tag args =>
      intro ψ _
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.Prim tag args)
            ψ
          =
        qs.eval (Gate.Prim tag args) ψ
      exact
        LowerGateClass.evalL_Prim
          (qs := qs)
          tag
          args
          ψ
  | ShiftL initSize r n =>
      intro ψ _
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.ShiftL r n)
            ψ
          =
        qs.eval (Gate.ShiftL r n) ψ
      exact
        LowerGateClass.evalL_shiftL
          (qs := qs)
          r n ψ
  | ShiftR initSize r n =>
      intro ψ _
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.ShiftR r n)
            ψ
          =
        qs.eval (Gate.ShiftR r n) ψ
      exact
        LowerGateClass.evalL_shiftR
          (qs := qs)
          r n ψ
  | Negate initSize r =>
      intro ψ _
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.Negate r)
            ψ
          =
        qs.eval (Gate.Negate r) ψ
      exact
        LowerGateClass.evalL_negate
          (qs := qs)
          r ψ
  | AddScaled initSize dst src negSrc shift =>
      intro ψ _
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.AddScaled
              dst src negSrc shift)
            ψ
          =
        qs.eval
          (Gate.AddScaled
            dst src negSrc shift)
          ψ
      exact
        LowerGateClass.evalL_addScaled
          (qs := qs)
          dst src negSrc shift ψ
  | zeroExtend initSize r n =>
      intro ψ _
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.zeroExtend r n)
            ψ
          =
        qs.eval (Gate.zeroExtend r n) ψ
      exact
        LowerGateClass.evalL_zeroExtend
          (qs := qs)
          r n ψ
  | signExtend initSize r n =>
      intro ψ _
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.signExtend r n)
            ψ
          =
        qs.eval (Gate.signExtend r n) ψ
      exact
        LowerGateClass.evalL_signExtend
          (qs := qs)
          r n ψ
  | zeroDealloc initSize r n =>
      intro ψ _
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.zeroDealloc r n)
            ψ
          =
        qs.eval (Gate.zeroDealloc r n) ψ
      exact
        LowerGateClass.evalL_zeroDealloc
          (qs := qs)
          r n ψ
  | signDealloc initSize r n =>
      intro ψ _
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.signDealloc r n)
            ψ
          =
        qs.eval (Gate.signDealloc r n) ψ
      exact
        LowerGateClass.evalL_signDealloc
          (qs := qs)
          r n ψ
  | RadixReverse initSize r m =>
      intro ψ _
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.RadixReverse r m)
            ψ
          =
        qs.eval (Gate.RadixReverse r m) ψ
      exact
        LowerGateClass.evalL_radixReverse
          (qs := qs)
          r m ψ
  | signedBase phi x z hstop =>
      intro ψ _
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.Naive_SignedPhaseProd
              phi x z)
            ψ
          =
        qs.eval
          (Gate.SignedPhaseProd phi x z)
          ψ
      exact
        LowerGateClass.evalL_naive_signedPhaseProd
          (qs := qs)
          phi x z ψ
  | signedStep
      phi x z layout
      hrec hcapacity child ihChild =>
      intro ψ hready
      change
        CleanWorkspaceState
            qs
            (initSignedLayoutState layout)
            (scanNeededWidths x z ops)
            ψ
          ∧
        PhaseLoweringReady qs child ψ
        at hready
      rcases hready with ⟨hclean, hchild⟩
      change
        LowerGateClass.evalL
            (qs := qs)
            (lowerGateRec child)
            ψ
          =
        qs.eval
          (Gate.SignedPhaseProd phi x z)
          ψ
      calc
        LowerGateClass.evalL
            (qs := qs)
            (lowerGateRec child)
            ψ
            =
        qs.eval
            (compiledSignedPhaseGate
              k hk pts hpts ops
              phi x z layout)
            ψ :=
          ihChild ψ hchild
        _ =
        qs.eval
            (Gate.SignedPhaseProd phi x z)
            ψ :=
          eval_compiledSignedPhaseGate_correct
            qs k hk pts hpts hInterp
            ops hC hRun
            phi x z layout ψ hclean
  | cSignedBase ctrl phi x z hstop =>
      intro ψ _
      change
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.Naive_CSignedPhaseProd
              ctrl phi x z)
            ψ
          =
        qs.eval
          (Gate.CSignedPhaseProd
            ctrl phi x z)
          ψ
      exact
        LowerGateClass.evalL_naive_csignedPhaseProd
          (qs := qs)
          ctrl phi x z ψ
  | cSignedStep
      ctrl phi x z layout
      hrec hcapacity hctrl child ihChild =>
      intro ψ hready
      change
        CleanWorkspaceState
            qs
            (initSignedLayoutState layout)
            (scanNeededWidths x z ops)
            ψ
          ∧
        PhaseLoweringReady qs child ψ
        at hready
      rcases hready with ⟨hclean, hchild⟩
      change
        LowerGateClass.evalL
            (qs := qs)
            (lowerGateRec child)
            ψ
          =
        qs.eval
          (Gate.CSignedPhaseProd
            ctrl phi x z)
          ψ
      calc
        LowerGateClass.evalL
            (qs := qs)
            (lowerGateRec child)
            ψ
            =
        qs.eval
            (compiledCSignedPhaseGate
              k hk pts hpts ops
              ctrl phi x z layout)
            ψ :=
          ihChild ψ hchild
        _ =
        qs.eval
            (Gate.CSignedPhaseProd
              ctrl phi x z)
            ψ :=
          eval_compiledCSignedPhaseGate_correct
            qs k hk pts hpts hInterp
            ops hC hRun
            ctrl phi x z layout hctrl
            ψ hclean

end Shor
