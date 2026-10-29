import ForShor.ShorVerification.Implementation.Compiler.Statement

/-!
# Compiler: the single-table forms

`GateWorkspaceOK`, `lowerGate` and `GateWorkspaceCleanState` for one fixed
Toom-Cook table, used by `Emit/`, `GateCount/` and `Reference/`, and the bridge
saying that at the constant policy of a table the policy workspace conditions
are that table's.
-/

namespace Shor

section
open Operations

/-- `Policy.GateWorkspaceOK` for a single table `ops`. -/
def GateWorkspaceOK {k : ℕ} (ops : Prog k) : Gate → Prop
  | Gate.seq U V => GateWorkspaceOK ops U ∧ GateWorkspaceOK ops V
  | Gate.adj U => GateWorkspaceOK ops U
  | Gate.QFT r => QFTReserveOK ops r
  | Gate.SignedPhaseProd _ x z => SignedRecursiveWorkspaceOK ops x z
  | Gate.CSignedPhaseProd ctrl _ x z => CSignedRecursiveWorkspaceOK ops ctrl x z
  | Gate.CmpGeConst N data scratch flag => ConstArithmeticWorkspace N data scratch flag
  | Gate.CSubConst N data scratch flag => ConstArithmeticWorkspace N data scratch flag
  | Gate.idealCtrlModMul _ _ _ _ => False
  | _ => True

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
def lowerGate
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (pts : List Point)
    (hpts : pts.length = q k) :
    (G : Gate) →
    GateWorkspaceOK ops G →
    LowGate

  | Gate.id, _ =>
      LowGate.id

  | Gate.seq U V, hworkspace =>
      LowGate.seq
        (lowerGate k hk ops pts hpts U hworkspace.1)
        (lowerGate k hk ops pts hpts V hworkspace.2)

  | Gate.adj U, hworkspace =>
      LowGate.adj
        (lowerGate k hk ops pts hpts U hworkspace)

  | Gate.H qbit, _ =>
      LowGate.H qbit

  | Gate.X qbit, _ =>
      LowGate.X qbit

  | Gate.CNOT ctrl target, _ =>
      LowGate.CNOT ctrl target

  | Gate.Toffoli c₁ c₂ target, _ =>
      LowGate.Toffoli c₁ c₂ target

  | Gate.QFT r, hworkspace =>
      lowerQFT
        k hk ops pts hpts r hworkspace

  | Gate.SignedPhaseProd phi x z, hworkspace =>
      lowerSignedPhaseProdWithWorkspace k hk phi x z ops pts hpts hworkspace

  | Gate.CSignedPhaseProd ctrl phi x z, hworkspace =>
      lowerCSignedPhaseProdWithWorkspace k hk ctrl phi x z ops pts hpts hworkspace

  | Gate.CmpGeConst N data scratch flag, hworkspace =>
      lowerCmpGeConst N data scratch flag hworkspace

  | Gate.CSubConst N data scratch flag, hworkspace =>
      lowerCSubConst N data scratch flag hworkspace

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

/--
Runtime cleanliness required before evaluating each recursively lowered node.

For a sequence, cleanliness is threaded through the first lowered component
before checking the second.  For adjoints, the condition is phrased on the state
that would appear before the forward circuit.  Primitive and direct low-level
constructors carry no recursive workspace-cleanliness obligation here.
-/
noncomputable def GateWorkspaceCleanState
    (qs : QSemantics)
    [RegEncoding qs.Basis]
    [GateSemanticsCore qs]
    [LowerGateClass qs]
    (k : ℕ)
    (hk : 1 < k)
    (ops : Prog k)
    (pts : List Point)
    (hpts : pts.length = q k) :
    (G : Gate) →
    GateWorkspaceOK ops G →
    qs.State →
    Prop

  | Gate.id, _, _ =>
      True

  | Gate.seq U V, hworkspace, ψ =>
      GateWorkspaceCleanState qs k hk ops pts hpts U hworkspace.1 ψ
        ∧
      GateWorkspaceCleanState qs k hk ops pts hpts V hworkspace.2
          (LowerGateClass.evalL (qs := qs)
            (lowerGate k hk ops pts hpts U hworkspace.1) ψ)

  | Gate.adj U, hworkspace, ψ =>
      GateWorkspaceCleanState qs k hk ops pts hpts U hworkspace (qs.eval (Gate.adj U) ψ)

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

  | Gate.CmpGeConst _ data scratch _, _, ψ =>
      CmpGeConstCleanState qs data scratch ψ

  | Gate.CSubConst N data scratch flag, _, ψ =>
      CSubConstCleanState qs N data scratch flag ψ

  | _, _, _ =>
      True

end

/-- At the constant policy, the policy reserve condition is the fixed table's. -/
theorem Policy.qftReserveOK_const_iff {T : ToomCookTable} {r : ExtReg} :
    Policy.QFTReserveOK (ShorLoweringPolicy.constPolicy T) r
      ↔ _root_.Shor.QFTReserveOK T.ops r := by
  unfold Policy.QFTReserveOK _root_.Shor.QFTReserveOK
  rw [Policy.qftWorkspaceNeed_const]

/-- Bridge: at the constant policy the two static predicates agree. -/
theorem Policy.gateWorkspaceOK_const_iff {T : ToomCookTable} :
    ∀ G : Gate,
      Policy.GateWorkspaceOK (ShorLoweringPolicy.constPolicy T) G
        ↔ _root_.Shor.GateWorkspaceOK T.ops G
  | Gate.seq U V => by
      simp only [Policy.GateWorkspaceOK, _root_.Shor.GateWorkspaceOK]
      rw [Policy.gateWorkspaceOK_const_iff U, Policy.gateWorkspaceOK_const_iff V]
  | Gate.adj U => by
      simp only [Policy.GateWorkspaceOK, _root_.Shor.GateWorkspaceOK]
      rw [Policy.gateWorkspaceOK_const_iff U]
  | Gate.QFT r => Policy.qftReserveOK_const_iff
  | Gate.SignedPhaseProd _ x z => Policy.workspaceOK_const_iff
  | Gate.CSignedPhaseProd ctrl _ x z => Policy.cWorkspaceOK_const_iff
  | Gate.CmpGeConst .. => Iff.rfl
  | Gate.CSubConst .. => Iff.rfl
  | Gate.idealCtrlModMul .. => Iff.rfl
  | Gate.id => Iff.rfl
  | Gate.H _ => Iff.rfl
  | Gate.X _ => Iff.rfl
  | Gate.CNOT .. => Iff.rfl
  | Gate.Toffoli .. => Iff.rfl
  | Gate.ShiftL .. => Iff.rfl
  | Gate.ShiftR .. => Iff.rfl
  | Gate.Negate _ => Iff.rfl
  | Gate.AddScaled .. => Iff.rfl
  | Gate.zeroExtend .. => Iff.rfl
  | Gate.signExtend .. => Iff.rfl
  | Gate.zeroDealloc .. => Iff.rfl
  | Gate.signDealloc .. => Iff.rfl
  | Gate.RadixReverse .. => Iff.rfl

end Shor
