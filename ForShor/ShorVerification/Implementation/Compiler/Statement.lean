import ForShor.ShorVerification.Framework.Semantics.LowGateSemantics
import ForShor.ShorVerification.Framework.ToomCookTable
import ForShor.ShorVerification.Framework.Semantics.GateSemantics
import Mathlib.Data.Nat.BitIndices
import ForShor.ShorVerification.Implementation.PhaseProduct.Statement
import ForShor.ShorVerification.Implementation.QFT.Statement

/-!
# Compiler: lowering `Gate` to `LowGate` and its correctness statement

Everything needed to state the proposition proved in `Main.lean`: the
lowering of the constant-arithmetic gates, the condition that a gate has the
workspace its lowering needs, the lowering itself, the clean-state
precondition, and the correctness claim.
-/

universe u

namespace Shor

/-! =========================================================
    Constant arithmetic
========================================================= -/

section
open LowGate

/-- Static physical conditions needed by the concrete constant-arithmetic
lowerers.  Cleanliness is deliberately kept out of this record. -/
structure ConstArithmeticWorkspace (N : ℕ) (data scratch : ExtReg) (flag : ℕ) : Prop where
  data_can_grow : data.CanGrow 1
  scratch_can_grow : scratch.CanGrow 1
  data_scratch_disjoint : data.OwnedDisjoint scratch
  flag_not_data : flag ∉ data.ownedQubits
  flag_not_scratch : flag ∉ scratch.ownedQubits
  scratch_positive : 0 < scratch.width
  constant_fits : N < 2 ^ (scratch.width - 1)
  data_width_fits : data.width ≤ scratch.width - 1

/-- The first genuinely allocated reserve qubit of `scratch`. -/
def constArithmeticUnitQubit (scratch : ExtReg) (h : scratch.CanGrow 1) : ℕ :=
  (scratch.newBits 1).get
    ⟨0, by
      have hsize : regSize (scratch.newBits 1) = 1 := by
        simp [ExtReg.newBits, ExtReg.CanGrow, ExtReg.capacity, regSize, Reg.width, Reg.take] at h ⊢
        omega
      have hwidth : (scratch.newBits 1).width = 1 := by simpa [regSize] using hsize
      omega⟩

/-- Regard the one-bit constant workspace as a signed extendable register. -/
def constArithmeticUnit (scratch : ExtReg) (h : scratch.CanGrow 1) : ExtReg :=
  ExtReg.ofReg (qubitReg (constArithmeticUnitQubit scratch h))

/-- Copy a classical bit pattern into `dst`, controlled by one physical qubit.
Out-of-range indices are ignored; the workspace proof later shows that every
bit of the chosen constant is in range. -/
def lowerCopyBitPowers
    (dst : ExtReg) (ctrl : ℕ) : List ℕ → LowGate
  | [] => LowGate.id
  | i :: bits =>
      if hi : i < dst.width then
        LowGate.CNOT ctrl
          (dst.active.get
            ⟨i, by simpa [ExtReg.width] using! hi⟩) ;;
        lowerCopyBitPowers dst ctrl bits
      else
        lowerCopyBitPowers dst ctrl bits

/-- Controlled-write the binary expansion of `N` into a clean register. -/
def lowerCopyConstFromUnit (N : ℕ) (dst : ExtReg) (ctrl : ℕ) : LowGate :=
  lowerCopyBitPowers dst ctrl N.bitIndices

/-- Prepare `scratch = -N` from clean active scratch and one clean reserve bit.
The constant write is at most one CNOT per active bit; the final negation is
one linear-cost target operation. -/
def lowerPrepareNegConst (N : ℕ) (scratch : ExtReg) (h : scratch.CanGrow 1) : LowGate :=
  let q := constArithmeticUnitQubit scratch h
  LowGate.X q ;;
  lowerCopyConstFromUnit N scratch q ;;
  LowGate.Negate scratch

/-- Compare the unsigned active value of `data` against `N` and toggle `flag`
iff `N ≤ data`.  The extra data bit makes the source unsigned; `scratch` is
restored by the adjoint computation. -/
def lowerCmpGeConst (N : ℕ) (data scratch : ExtReg) (flag : ℕ)
    (h : ConstArithmeticWorkspace N data scratch flag) : LowGate :=
  let prep := lowerPrepareNegConst N scratch h.scratch_can_grow
  let sign := scratch.active.get
    ⟨scratch.width - 1, by
      have hlt : scratch.width - 1 < scratch.width :=
        Nat.sub_lt h.scratch_positive (by omega)
      simpa [ExtReg.width, regSize] using hlt⟩
  let diff :=
    LowGate.zeroExtend data 1 ;;
    LowGate.AddScaled scratch (data.grow 1) false 0 ;;
    LowGate.zeroDealloc data 1
  prep ;;
  diff ;;
  (LowGate.X flag ;; LowGate.CNOT sign flag) ;;
  †diff ;;
  †prep

/-- Conditionally subtract `N` modulo the active width of `data`.  The control
prepares `scratch` as either `0` or `-N`; one fixed-width `AddScaled` performs
the modular subtraction, and the preparation is then uncomputed. -/
def lowerCSubConst (N : ℕ) (data scratch : ExtReg) (flag : ℕ)
    (h : ConstArithmeticWorkspace N data scratch flag) : LowGate :=
  let q := constArithmeticUnitQubit scratch h.scratch_can_grow
  let prep := LowGate.CNOT flag q ;; lowerCopyConstFromUnit N scratch q ;; LowGate.Negate scratch
  prep ;;
  LowGate.AddScaled data scratch false 0 ;;
  †prep

/-- Basis-level cleanliness consumed by both Step-3 lowerers. -/
def ConstArithmeticCleanBasis
    {Basis : Type u} [RegEncoding Basis] (data scratch : ExtReg) (b : Basis) : Prop :=
  data.FreshFor 1 b ∧ extToInt scratch b = 0 ∧ scratch.FreshFor 1 b

/-- Basis-level cleanliness consumed by controlled subtraction.  The concrete
lowerer performs fixed-width modular subtraction, so it is total on every
control/data value and needs no hidden no-underflow premise. -/
def CSubConstCleanBasis {Basis : Type u} [RegEncoding Basis]
    (_N : ℕ) (data scratch : ExtReg) (_flag : ℕ) (b : Basis) : Prop :=
  ConstArithmeticCleanBasis data scratch b

/-- Linear closure of clean comparison inputs. -/
abbrev CmpGeConstCleanState
    (qs : QSemantics) [RegEncoding qs.Basis] (data scratch : ExtReg) : qs.State → Prop :=
  CleanClosure (ConstArithmeticCleanBasis data scratch)

/-- Linear closure of clean controlled-subtraction inputs. -/
abbrev CSubConstCleanState (qs : QSemantics) [RegEncoding qs.Basis]
    (N : ℕ) (data scratch : ExtReg) (flag : ℕ) : qs.State → Prop :=
  CleanClosure (CSubConstCleanBasis N data scratch flag)

end

/-! =========================================================
    Static workspace condition
========================================================= -/

section
open Operations

/-- Every QFT, phase-product and modular-arithmetic block in a gate has the
workspace its lowerer needs under the policy `P`. -/
def Policy.GateWorkspaceOK (P : ShorLoweringPolicy) : Gate → Prop
  | Gate.seq U V => Policy.GateWorkspaceOK P U ∧ Policy.GateWorkspaceOK P V
  | Gate.adj U => Policy.GateWorkspaceOK P U
  | Gate.QFT r => Policy.QFTReserveOK P r
  | Gate.SignedPhaseProd _ x z => Policy.WorkspaceOK P x z
  | Gate.CSignedPhaseProd ctrl _ x z => Policy.CWorkspaceOK P ctrl x z
  | Gate.CmpGeConst N data scratch flag => ConstArithmeticWorkspace N data scratch flag
  | Gate.CSubConst N data scratch flag => ConstArithmeticWorkspace N data scratch flag
  | Gate.idealCtrlModMul _ _ _ _ => False
  | _ => True

end

/-! =========================================================
    The lowering
========================================================= -/

section
open Operations

/-- Lower a gate to `LowGate`, sending each QFT, phase-product and
modular-arithmetic block to its subroutine's lowerer. -/
def Policy.lowerGate (P : ShorLoweringPolicy) :
    (G : Gate) → Policy.GateWorkspaceOK P G → LowGate
  | Gate.id, _ => LowGate.id
  | Gate.seq U V, hworkspace =>
      LowGate.seq (Policy.lowerGate P U hworkspace.1) (Policy.lowerGate P V hworkspace.2)
  | Gate.adj U, hworkspace => LowGate.adj (Policy.lowerGate P U hworkspace)
  | Gate.H qbit, _ => LowGate.H qbit
  | Gate.X qbit, _ => LowGate.X qbit
  | Gate.CNOT ctrl target, _ => LowGate.CNOT ctrl target
  | Gate.Toffoli c₁ c₂ target, _ => LowGate.Toffoli c₁ c₂ target
  | Gate.QFT r, hworkspace => Policy.lowerQFT P r hworkspace
  | Gate.SignedPhaseProd phi x z, _ => Policy.lowerSignedPhaseProd P phi x z
  | Gate.CSignedPhaseProd ctrl phi x z, _ =>
      Policy.lowerCSignedPhaseProd P ctrl phi x z
  | Gate.CmpGeConst N data scratch flag, hworkspace =>
      lowerCmpGeConst N data scratch flag hworkspace
  | Gate.CSubConst N data scratch flag, hworkspace =>
      lowerCSubConst N data scratch flag hworkspace
  | Gate.ShiftL r n, _ => LowGate.ShiftL r n
  | Gate.ShiftR r n, _ => LowGate.ShiftR r n
  | Gate.Negate r, _ => LowGate.Negate r
  | Gate.AddScaled dst src negSrc shift, _ => LowGate.AddScaled dst src negSrc shift
  | Gate.zeroExtend r n, _ => LowGate.zeroExtend r n
  | Gate.signExtend r n, _ => LowGate.signExtend r n
  | Gate.zeroDealloc r n, _ => LowGate.zeroDealloc r n
  | Gate.signDealloc r n, _ => LowGate.signDealloc r n
  | Gate.RadixReverse r m, _ => LowGate.RadixReverse r m

end

/-! =========================================================
    Clean-state precondition
========================================================= -/

section
open Operations

/-- The spare qubits each lowered block will use are zero on the state it is
applied to. For a sequence, the second component's condition is checked on the
state after the first component's lowered circuit. -/
noncomputable def Policy.GateWorkspaceCleanState (qs : QSemantics) [RegEncoding qs.Basis]
    [GateSemanticsCore qs] [LowerGateClass qs] (P : ShorLoweringPolicy) :
    (G : Gate) → Policy.GateWorkspaceOK P G → qs.State → Prop
  | Gate.id, _, _ => True
  | Gate.seq U V, hworkspace, ψ =>
      Policy.GateWorkspaceCleanState qs P U hworkspace.1 ψ ∧
      Policy.GateWorkspaceCleanState qs P V hworkspace.2
        (LowerGateClass.evalL (qs := qs) (Policy.lowerGate P U hworkspace.1) ψ)
  | Gate.adj U, hworkspace, ψ =>
      Policy.GateWorkspaceCleanState qs P U hworkspace (qs.eval (Gate.adj U) ψ)
  | Gate.H _, _, _ => True
  | Gate.X _, _, _ => True
  | Gate.QFT r, _, ψ => QFTWorkspaceCleanState qs (Policy.qftXWork P r) (Policy.qftZWork P r) ψ
  | Gate.SignedPhaseProd _ x z, _, ψ => RecursiveWorkspaceCleanState qs x z ψ
  | Gate.CSignedPhaseProd _ _ x z, _, ψ => RecursiveWorkspaceCleanState qs x z ψ
  | Gate.CmpGeConst _ data scratch _, _, ψ => CmpGeConstCleanState qs data scratch ψ
  | Gate.CSubConst N data scratch flag, _, ψ => CSubConstCleanState qs N data scratch flag ψ
  | _, _, _ => True

end

/-! =========================================================
    Correctness
========================================================= -/

/-- For an admissible policy, the lowered program of a gate with enough
workspace acts on a clean state exactly as the gate does. -/
def Policy.LowerGateCorrect (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs]
    [LowerGateClass qs] (P : ShorLoweringPolicy) : Prop :=
  P.Admissible →
    ∀ (G : Gate) (hworkspace : Policy.GateWorkspaceOK P G) (ψ : qs.State),
      Policy.GateWorkspaceCleanState qs P G hworkspace ψ →
      ⟦Policy.lowerGate P G hworkspace⟧ₗ ψ = ⟦G⟧ ψ

end Shor
