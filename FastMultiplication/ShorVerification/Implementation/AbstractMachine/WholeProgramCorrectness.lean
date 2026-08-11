import FastMultiplication.ShorVerification.Implementation.AbstractMachine.QFTLoweringCorrectness.Readiness

namespace Shor

/-!
# Whole-Program Lowering

The public whole-program lowerer does not ask its caller to construct QFT or
phase-product lowering plans.  Instead, the caller proves one recursive static
workspace condition on the source gate.  At each QFT or signed-phase-product
node, that proof supplies the reserve-capacity facts needed by the already
defined concrete lowerer.

Cleanliness is deliberately absent from `GateWorkspaceOK`: it is a condition
on the input state, not a condition on the syntax or physical register layout.
It belongs in the later semantic-correctness theorem.
-/

universe u

/-! =========================================================
    Section 1: Static workspace precondition
========================================================= -/

/--
Every recursively lowered node in `G` has enough concrete physical workspace.

* A QFT register has enough inactive reserve for the two workspace pools
  selected by `lowerQFT`.
* A signed phase product has enough mutually disjoint reserve for its complete
  recursion.
* A controlled signed phase product additionally keeps its control qubit
  outside both operands' complete owned regions.
* Sequential composition and adjoint recurse structurally.

The remaining constructors lower directly and need no reserve.
-/
def GateWorkspaceOK
    {k : ℕ}
    (ops : Prog k) :
    Gate → Prop

  | Gate.seq U V =>
      GateWorkspaceOK ops U ∧ GateWorkspaceOK ops V

  | Gate.adj U =>
      GateWorkspaceOK ops U

  | Gate.QFT r =>
      QFTReserveOK ops r

  | Gate.SignedPhaseProd _ x z =>
      SignedRecursiveWorkspaceOK ops x z

  | Gate.CSignedPhaseProd ctrl _ x z =>
      CSignedRecursiveWorkspaceOK ops ctrl x z

  | _ =>
      True

namespace GateWorkspaceOK

theorem left
    {k : ℕ}
    {ops : Prog k}
    {U V : Gate}
    (h : GateWorkspaceOK ops (Gate.seq U V)) :
    GateWorkspaceOK ops U :=
  h.1

theorem right
    {k : ℕ}
    {ops : Prog k}
    {U V : Gate}
    (h : GateWorkspaceOK ops (Gate.seq U V)) :
    GateWorkspaceOK ops V :=
  h.2

theorem of_adj
    {k : ℕ}
    {ops : Prog k}
    {U : Gate}
    (h : GateWorkspaceOK ops (Gate.adj U)) :
    GateWorkspaceOK ops U :=
  h

theorem qft
    {k : ℕ}
    {ops : Prog k}
    {r : ExtReg}
    (h : GateWorkspaceOK ops (Gate.QFT r)) :
    QFTReserveOK ops r :=
  h

theorem signedPhaseProd
    {k : ℕ}
    {ops : Prog k}
    {phi : ℝ}
    {x z : ExtReg}
    (h :
      GateWorkspaceOK
        ops
        (Gate.SignedPhaseProd phi x z)) :
    SignedRecursiveWorkspaceOK ops x z :=
  h

theorem cSignedPhaseProd
    {k : ℕ}
    {ops : Prog k}
    {ctrl : ℕ}
    {phi : ℝ}
    {x z : ExtReg}
    (h :
      GateWorkspaceOK
        ops
        (Gate.CSignedPhaseProd ctrl phi x z)) :
    CSignedRecursiveWorkspaceOK ops ctrl x z :=
  h

end GateWorkspaceOK

/-! =========================================================
    Section 2: Whole-program lowering
========================================================= -/

/--
Lower an arbitrary high-level gate whose recursive workspace is large enough.

The proof parameter contains no lowering plan.  It supplies only the static
reserve and disjointness facts consumed by the concrete QFT and phase-product
lowerers.

The controlled signed-phase-product branch currently uses the naive controlled
leaf.  The phase-product layer has a controlled plan-directed lowerer, but it
does not yet have the analogue of `standardSignedPhaseLoweringPlan` which
constructs that plan solely from `CSignedRecursiveWorkspaceOK`.  Once that
constructor is added, only this branch needs to change.
-/
noncomputable def lowerGate
    {Basis : Type u}
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k) :
    (G : Gate) →
    GateWorkspaceOK ops G →
    LowGate

  | Gate.id, _ =>
      LowGate.id

  | Gate.seq U V, hworkspace =>
      LowGate.seq
        (lowerGate (Basis := Basis) k hk ops U hworkspace.1)
        (lowerGate (Basis := Basis) k hk ops V hworkspace.2)

  | Gate.adj U, hworkspace =>
      LowGate.adj
        (lowerGate (Basis := Basis) k hk ops U hworkspace)

  | Gate.H qbit, _ =>
      LowGate.H qbit

  | Gate.X qbit, _ =>
      LowGate.X qbit

  | Gate.QFT r, hworkspace =>
      lowerQFT
        k hk ops r hworkspace

  | Gate.SignedPhaseProd phi x z, hworkspace =>
      lowerSignedPhaseProdWithWorkspace k hk phi x z ops hworkspace

  | Gate.CSignedPhaseProd ctrl phi x z, hworkspace =>
    lowerCSignedPhaseProdWithWorkspace k hk ctrl phi x z ops hworkspace

  | Gate.Prim tag args, _ =>
      LowGate.Prim tag args

  | Gate.ShiftL r n, _ =>
      LowGate.ShiftL r n

  | Gate.ShiftR r n, _ =>
      LowGate.ShiftR r n

  | Gate.Negate r, _ =>
      LowGate.Negate r

  | Gate.AddScaled dst src negSrc shift, _ =>
      LowGate.AddScaled
        dst src negSrc shift

  | Gate.zeroExtend r n, _ =>
      LowGate.zeroExtend r n

  | Gate.signExtend r n, _ =>
      LowGate.signExtend r n

  | Gate.zeroDealloc r n, _ =>
      LowGate.zeroDealloc r n

  | Gate.signDealloc r n, _ =>
      LowGate.signDealloc r n

  | Gate.RadixReverse r m, _ =>
      LowGate.RadixReverse r m

/-! =========================================================
    Section 3: Definitional equations
========================================================= -/

@[simp] theorem lowerGate_id
    {Basis : Type u}
    {k : ℕ}
    (hk : 1 < k)
    (ops : Prog k)
    (hworkspace : GateWorkspaceOK ops Gate.id) :
    lowerGate
        (Basis := Basis)
        k hk ops Gate.id hworkspace
      =
    LowGate.id := by
  rfl

@[simp] theorem lowerGate_seq
    {Basis : Type u}
    {k : ℕ}
    (hk : 1 < k)
    (ops : Prog k)
    (U V : Gate)
    (hworkspace :
      GateWorkspaceOK ops (Gate.seq U V)) :
    lowerGate
        (Basis := Basis)
        k hk ops
        (Gate.seq U V)
        hworkspace
      =
    LowGate.seq
      (lowerGate
        (Basis := Basis)
        k hk ops U hworkspace.1)
      (lowerGate
        (Basis := Basis)
        k hk ops V hworkspace.2) := by
  rfl

@[simp] theorem lowerGate_QFT
    {Basis : Type u}
    {k : ℕ}
    (hk : 1 < k)
    (ops : Prog k)
    (r : ExtReg)
    (hworkspace :
      GateWorkspaceOK ops (Gate.QFT r)) :
    lowerGate
        (Basis := Basis)
        k hk ops
        (Gate.QFT r)
        hworkspace
      =
    lowerQFT k hk ops r hworkspace := by
  rfl

@[simp] theorem lowerGate_SignedPhaseProd
    {Basis : Type u}
    {k : ℕ}
    (hk : 1 < k)
    (ops : Prog k)
    (phi : ℝ)
    (x z : ExtReg)
    (hworkspace :
      GateWorkspaceOK
        ops
        (Gate.SignedPhaseProd phi x z)) :
    lowerGate
        (Basis := Basis)
        k hk ops
        (Gate.SignedPhaseProd phi x z)
        hworkspace
      =
    lowerSignedPhaseProdWithWorkspace
      k hk phi x z ops hworkspace := by
  rfl

@[simp] theorem lowerGate_CSignedPhaseProd
    {Basis : Type u}
    {k : ℕ}
    (hk : 1 < k)
    (ops : Prog k)
    (ctrl : ℕ)
    (phi : ℝ)
    (x z : ExtReg)
    (hworkspace :
      GateWorkspaceOK
        ops
        (Gate.CSignedPhaseProd ctrl phi x z)) :
    lowerGate
        (Basis := Basis)
        k hk ops
        (Gate.CSignedPhaseProd ctrl phi x z)
        hworkspace
      =
    lowerCSignedPhaseProdWithWorkspace
      k hk ctrl phi x z ops hworkspace := by
  rfl


noncomputable def GateWorkspaceCleanState
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [LowerGateClass qs]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k) :
    (G : Gate) →
    GateWorkspaceOK ops G →
    qs.State →
    Prop

  | Gate.id, _, _ =>
      True

  | Gate.seq U V, hworkspace, ψ =>
      GateWorkspaceCleanState qs k hk ops U hworkspace.1 ψ
        ∧
      GateWorkspaceCleanState qs k hk ops V hworkspace.2
          (LowerGateClass.evalL (qs := qs)
            (lowerGate (Basis := qs.Basis)  k hk ops U hworkspace.1) ψ)

    | Gate.adj U, hworkspace, ψ =>
      GateWorkspaceCleanState  qs k hk ops U hworkspace (qs.eval (Gate.adj U) ψ)

  | Gate.H _, _, _ =>
      True

  | Gate.X _, _, _ =>
      True

  | Gate.QFT r, _, ψ =>
      QFTWorkspaceCleanState qs (qftXWork ops r) (qftZWork ops r) ψ

  | Gate.SignedPhaseProd _ x z, _, ψ =>
      RecursiveWorkspaceCleanState qs x z ψ

  | Gate.CSignedPhaseProd _ _ x z, _, ψ =>
      RecursiveWorkspaceCleanState qs x z ψ

  | _, _, _ =>
      True

/--
Whole-program lowering correctness.

The static hypothesis `hworkspace` guarantees that every QFT and recursive
phase-product register contains enough concrete reserve.

The dynamic hypothesis `hclean` guarantees that the relevant reserve is clean
at the exact state where each lowered subprogram begins.
-/
theorem lowerGate_correctness
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsFacts qs]
    [LowerGateClass qs]
    [LowerGateGateBridge qs]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (hC : ProgConsumesPtsSafe (k := k) (by omega) State.start_state ops (genInterpolationPoints k))
    (hRun : run? ops State.start_state = some State.start_state)
    (G : Gate)
    (hworkspace : GateWorkspaceOK ops G)
    (ψ : qs.State)
    (hclean : GateWorkspaceCleanState qs k hk ops G hworkspace ψ) :
    LowerGateClass.evalL (qs := qs) (lowerGate (Basis := qs.Basis) k hk ops G hworkspace) ψ
      =
    qs.eval G ψ := by
  induction G generalizing ψ with

  | id =>
      have:=(LowerGateClass.evalL_id (qs := qs) ψ)
      simp[this, QSemantics.eval_id]

  | seq U V ihU ihV =>
      change
        GateWorkspaceCleanState
            qs k hk ops
            U
            hworkspace.1
            ψ
          ∧
        GateWorkspaceCleanState
            qs k hk ops
            V
            hworkspace.2
            (LowerGateClass.evalL
              (qs := qs)
              (lowerGate
                (Basis := qs.Basis)
                k hk ops
                U
                hworkspace.1)
              ψ)
        at hclean

      rcases hclean with
        ⟨hcleanU, hcleanV⟩

      have hUcorrect :
          LowerGateClass.evalL
              (qs := qs)
              (lowerGate
                (Basis := qs.Basis)
                k hk ops
                U
                hworkspace.1)
              ψ
            =
          qs.eval U ψ := by
        exact
          ihU
            hworkspace.1
            ψ
            hcleanU

      have hcleanV' :
          GateWorkspaceCleanState
            qs k hk ops
            V
            hworkspace.2
            (qs.eval U ψ) := by
        simpa only [hUcorrect] using hcleanV

      calc
        LowerGateClass.evalL
            (qs := qs)
            (lowerGate
              (Basis := qs.Basis)
              k hk ops
              (Gate.seq U V)
              hworkspace)
            ψ
            =
          LowerGateClass.evalL
            (qs := qs)
            (lowerGate
              (Basis := qs.Basis)
              k hk ops
              V
              hworkspace.2)
            (LowerGateClass.evalL
              (qs := qs)
              (lowerGate
                (Basis := qs.Basis)
                k hk ops
                U
                hworkspace.1)
              ψ) := by
                exact
                  LowerGateClass.evalL_seq
                    (lowerGate
                      (Basis := qs.Basis)
                      k hk ops
                      U
                      hworkspace.1)
                    (lowerGate
                      (Basis := qs.Basis)
                      k hk ops
                      V
                      hworkspace.2)
                    ψ

        _ =
          LowerGateClass.evalL
            (qs := qs)
            (lowerGate
              (Basis := qs.Basis)
              k hk ops
              V
              hworkspace.2)
            (qs.eval U ψ) := by
              rw [hUcorrect]

        _ =
          qs.eval V (qs.eval U ψ) := by
            exact
              ihV
                hworkspace.2
                (qs.eval U ψ)
                hcleanV'

        _ =
          qs.eval (Gate.seq U V) ψ := by
            exact
              (qs.eval_seq U V ψ).symm

    | adj U ihU =>
      change
        GateWorkspaceCleanState
          qs k hk ops U hworkspace
          (qs.eval (Gate.adj U) ψ)
        at hclean

      let φ : qs.State :=
        qs.eval (Gate.adj U) ψ

      have hforward :
          LowerGateClass.evalL
              (qs := qs)
              (lowerGate
                (Basis := qs.Basis)
                k hk ops U hworkspace)
              φ
            =
          ψ := by
        calc
          LowerGateClass.evalL
              (qs := qs)
              (lowerGate
                (Basis := qs.Basis)
                k hk ops U hworkspace)
              φ
              =
            qs.eval U φ := by
              exact ihU hworkspace φ hclean
          _ = ψ := by
            exact qs.eval_apply_adj U ψ

      calc
        LowerGateClass.evalL
            (qs := qs)
            (LowGate.adj
              (lowerGate
                (Basis := qs.Basis)
                k hk ops U hworkspace))
            ψ
            =
          LowerGateClass.evalL
            (qs := qs)
            (LowGate.adj
              (lowerGate
                (Basis := qs.Basis)
                k hk ops U hworkspace))
            (LowerGateClass.evalL
              (qs := qs)
              (lowerGate
                (Basis := qs.Basis)
                k hk ops U hworkspace)
              φ) := by
                rw [hforward]

        _ = φ := by
          exact
            LowerGateClass.evalL_adj_apply
              (qs := qs)
              (lowerGate
                (Basis := qs.Basis)
                k hk ops U hworkspace)
              φ

        _ = qs.eval (Gate.adj U) ψ := rfl

  | H qbit =>
      simpa only [lowerGate] using
        (LowerGateClass.evalL_H
          (qs := qs)
          qbit
          ψ)

  | X qbit =>
      simpa only [lowerGate] using
        (LowerGateClass.evalL_X
          (qs := qs)
          qbit
          ψ)

  | QFT r =>
      change
        QFTWorkspaceCleanState
          qs
          (qftXWork ops r)
          (qftZWork ops r)
          ψ
        at hclean

      simpa only [lowerGate] using
        (evalL_lowerQFT qs k hk ops r
          ψ
          {
            static := hworkspace
            clean := hclean
          }
          hC
          hRun)

  | SignedPhaseProd phi x z =>
      change
        RecursiveWorkspaceCleanState
          qs x z ψ
        at hclean

      simpa only [lowerGate] using
        (evalL_lowerSignedPhaseProd qs k hk phi x z ops ψ
          {
            static := hworkspace
            clean := hclean
          }
          hC
          hRun)

    | CSignedPhaseProd ctrl phi x z =>
      change
        RecursiveWorkspaceCleanState
          qs x z ψ
        at hclean

      simpa only [lowerGate] using
        (evalL_lowerCSignedPhaseProd qs k hk ctrl phi x z ops ψ
          {
            static := hworkspace
            clean := hclean
          }
          hC
          hRun)

  | Prim tag args =>
      simpa only [lowerGate] using
        (LowerGateClass.evalL_Prim
          (qs := qs)
          tag
          args
          ψ)

  | ShiftL r n =>
      simpa only [lowerGate] using
        (LowerGateClass.evalL_shiftL
          (qs := qs)
          r
          n
          ψ)

  | ShiftR r n =>
      simpa only [lowerGate] using
        (LowerGateClass.evalL_shiftR
          (qs := qs)
          r
          n
          ψ)

  | Negate r =>
      simpa only [lowerGate] using
        (LowerGateClass.evalL_negate
          (qs := qs)
          r
          ψ)

  | AddScaled dst src negSrc shift =>
      simpa only [lowerGate] using
        (LowerGateClass.evalL_addScaled
          (qs := qs)
          dst
          src
          negSrc
          shift
          ψ)

  | zeroExtend r n =>
      simpa only [lowerGate] using
        (LowerGateClass.evalL_zeroExtend
          (qs := qs)
          r
          n
          ψ)

  | signExtend r n =>
      simpa only [lowerGate] using
        (LowerGateClass.evalL_signExtend
          (qs := qs)
          r
          n
          ψ)

  | zeroDealloc r n =>
      simpa only [lowerGate] using
        (LowerGateClass.evalL_zeroDealloc
          (qs := qs)
          r
          n
          ψ)

  | signDealloc r n =>
      simpa only [lowerGate] using
        (LowerGateClass.evalL_signDealloc
          (qs := qs)
          r
          n
          ψ)

  | RadixReverse r m =>
      simpa only [lowerGate] using
        (LowerGateClass.evalL_radixReverse
          (qs := qs)
          r
          m
          ψ)

end Shor
