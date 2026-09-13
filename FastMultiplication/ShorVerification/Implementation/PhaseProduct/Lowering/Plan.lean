import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Compile
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Gates.NaiveLeaf

namespace Shor
open Gate
open Operations

/-!
# Phase-Product Lowering Definitions

This first block names the compiled gates that recursive lowering steps point
to. The actual lowering plan type appears below; these names must come first
because the recursive plan constructors refer to them.
-/

/-! =========================================================
    Compiled gate packages

    These definitions package the phase coefficients and compiled signed gates
    that the lowering proof treats as the replacement for primitive phase-product
    gates.
========================================================= -/

/-- Interpolation coefficients used by the lowered phase-product implementation. -/
def loweringPhaseCoeff (k : ℕ) (x z : ExtReg) (pts : List Point) (hpts : pts.length = q k) : Fin (q k) → ℚ :=
  cramerCoeffFromPtsWidth k (phaseLimbWidth x z k) pts hpts

/-- Compiled replacement for an uncontrolled signed phase-product gate. -/
def compiledSignedPhaseGate
    (k : ℕ)
    (hk : 1 < k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (ops : Prog k)
    (phi : Angle)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k) :
    Gate :=
  compileOpsToSignedGate k hk phi x z layout (loweringPhaseCoeff k x z pts hpts) ops

/-- Compiled replacement for a controlled signed phase-product gate. -/
def compiledCSignedPhaseGate
    (k : ℕ)
    (hk : 1 < k)
    (pts : List Point)
    (hpts : pts.length = q k)
    (ops : Prog k)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (layout : Gate.PhaseProductLayout x z k) :
    Gate :=
  compileOpsToCSignedGate k hk ctrl phi x z layout (loweringPhaseCoeff k x z pts hpts) ops
open scoped BigOperators

end Shor

namespace Shor
open Gate
open Operations

/-!
# Phase-Product Lowering Plans

This file now reads in the same order as the lowering pipeline:

1. the plan language;
2. the interpreter that erases a plan to a `LowGate`;
3. the standard interpolation-point wrapper used by public lowerers;
4. plan builders for allocation, deallocation, and annotated program bodies;
5. one-level compiled phase-product plans;
6. canonical recursive signed and controlled signed phase-product plans.
-/

/-! =========================================================
    The lowering-plan language

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
      (phi : Angle) (x z : ExtReg)
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
      (phi : Angle)
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
      (phi : Angle)
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
      (phi : Angle)
      (x z : ExtReg)
      (layout : Gate.PhaseProductLayout x z k)
      (hrec : nextSignedWidth x z ops < initSize)
      (hcapacity : (initSignedLayoutState layout).CanGrowToNeeds (scanNeededWidths x z ops))
      (hctrl : layout.ControlDisjoint ctrl)
      (child : PhaseLoweringPlan k hk pts hpts ops (nextSignedWidth x z ops)
          (compiledCSignedPhaseGate k hk pts hpts ops ctrl phi x z layout)) :
      PhaseLoweringPlan k hk pts hpts ops initSize (Gate.CSignedPhaseProd ctrl phi x z)

/-! =========================================================
    Plan-directed recursive lowering

    Interpreting a plan erases the proof data and returns the low-level gate
    chosen by the plan.
========================================================= -/

/--
Interpret a finite phase-lowering plan as a low-level circuit.
Termination is structural on `plan`. In a recursive phase-product case, the
child plan already contains the concrete layout and capacity proof required
for the next recursive call.
-/
def lowerGateRec
    {k : ℕ}
    {hk : 1 < k}
    {pts : List Point}
    {hpts : pts.length = q k}
    {ops : Prog k}
    {initSize : ℕ}
    {U : Gate}
    (plan : PhaseLoweringPlan k hk pts hpts ops initSize U) :
    LowGate :=
  match plan with
  | .id _ => LowGate.id
  | .seq left right => LowGate.seq (lowerGateRec left) (lowerGateRec right)
  | .H _ qbit => LowGate.H qbit
  | .X _ qbit => LowGate.X qbit
  | .ShiftL _ r n => LowGate.ShiftL r n
  | .ShiftR _ r n => LowGate.ShiftR r n
  | .Negate _ r => LowGate.Negate r
  | .AddScaled _ dst src negSrc shift => LowGate.AddScaled dst src negSrc shift
  | .zeroExtend _ r n => LowGate.zeroExtend r n
  | .signExtend _ r n => LowGate.signExtend r n
  | .zeroDealloc _ r n => LowGate.zeroDealloc r n
  | .signDealloc _ r n => LowGate.signDealloc r n
  | .RadixReverse _ r m => LowGate.RadixReverse r m
  | .signedBase phi x z _ => LowGate.Naive_SignedPhaseProd phi x z
  | .signedStep phi x z _layout _hrec _hcapacity child => lowerGateRec child
  | .cSignedBase ctrl phi x z _ => LowGate.Naive_CSignedPhaseProd ctrl phi x z
  | .cSignedStep ctrl phi x z _layout _hrec _hcapacity _hctrl child => lowerGateRec child

/-! =========================================================
    Standard interpolation-point public interface

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
def lowerPhasePlan
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
def lowerSignedPhaseProd
    (k : ℕ)
    (hk : 1 < k)
    (phi : Angle)
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
def lowerCSignedPhaseProd
    (k : ℕ)
    (hk : 1 < k)
    (ctrl : ℕ)
    (phi : Angle)
    (x z : ExtReg)
    (ops : Prog k)
    (plan : StandardPhaseLoweringPlan k hk ops (phaseInputSize x z)
        (Gate.CSignedPhaseProd ctrl phi x z)) :
    LowGate :=
  lowerGateRec plan

end Shor
