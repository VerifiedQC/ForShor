import ForShor.ShorVerification.Implementation.QubitCount.Statement

/-!
# Qubit count: the budgets in the walk's own shape

The budgets as the walk proofs produce them: `peakReserve` by well-founded
recursion on the width through the compiler's `nextWidthBy` and
`immediateNeedBy`, `qftPeakOf` over the whole halving tree. `Arith.lean`
proves them equal to the budgets of `Statement.lean`.
-/

namespace Shor

open Operations in
/-- The scratch one table operation charges on chunks of width `W`: a negation
its constant register and carry, an addition its carry. -/
def Policy.opScratch {k : ℕ} : valid_ops k → ℕ → ℕ
  | .negate _, W => W + 1
  | .addScaled _ _ _ _, _ => 1
  | _, _ => 0

/-- The largest scratch any operation of a table charges, on chunks of
width `W`. -/
def Policy.opsScratch {k : ℕ} : Prog k → ℕ → ℕ
  | [], _ => 0
  | op :: rest, W => max (Policy.opScratch op W) (Policy.opsScratch rest W)

namespace QubitCount
namespace Rec

open RecursivePhaseWorkspace (immediateXNeed immediateZNeed)

/-- Peak extra qubits of one lowered signed phase product on operands of widths
`wx` and `wz`: a recursive level activates the growth of its `k` chunk pairs,
then the larger of one child's peak and its body's scratch. -/
def peakReserve (P : ShorLoweringPolicy) (wx wz : ℕ) : ℕ :=
  match P.choose (max wx wz) with
  | none => 0
  | some T =>
    let Wnext := RecursivePhaseWorkspace.nextWidthBy P.widthRule T.ops wx wz
    if _hrec : Wnext < max wx wz then
      RecursivePhaseWorkspace.immediateXNeedBy P.widthRule T.ops wx wz
        + RecursivePhaseWorkspace.immediateZNeedBy P.widthRule T.ops wx wz
        + max (peakReserve P Wnext Wnext) (Policy.opsScratch T.ops Wnext)
    else 0
termination_by max wx wz
decreasing_by simpa using _hrec

/-- Peak extra qubits of the lowered QFT on `n` qubits: a split runs the upper
half, then a phase product on the two halves each grown by one qubit, then the
lower half. -/
def qftPeakOf (pp : ℕ → ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 =>
      let total := n + 2
      let leftWidth := total / 2
      let rightWidth := total - leftWidth
      max (2 + pp (leftWidth + 1) (rightWidth + 1))
        (max (qftPeakOf pp leftWidth) (qftPeakOf pp rightWidth))
termination_by n => n

/-- `qftPeakOf` under the policy `P`. -/
def qftPeak (P : ShorLoweringPolicy) (n : ℕ) : ℕ :=
  qftPeakOf (peakReserve P) n

/-- `peakReserve` with the capacity arguments every phase-product cost takes. -/
def ppPeak (P : ShorLoweringPolicy) (wx _cx wz _cz : ℕ) : ℕ :=
  peakReserve P wx wz

/-- Peak extra qubits of each phase of one controlled modular multiplication
when a phase product on widths `wx`, `wz` and spare capacities `cx`, `cz`
peaks `pp wx cx wz cz`. -/
def modMulPhasePeaksWith (P : ShorLoweringPolicy) (pp : ℕ → ℕ → ℕ → ℕ → ℕ)
    (dW dC wW wC sW sC : ℕ) : List ℕ :=
  [ 2 + pp (dW + 1) (dC - 2) (wW + 1) (wC - 1)
  , qftPeak P wW
  , qftPeak P (dW + 1)
  , 2 + pp (wW + 1) (wC - 1) (dW + 2) (dC - 2)
  , sW + 2
  , qftPeak P sW
  , 2 + pp (wW + 1) (wC - 1) (sW + 1) (sC - 1)
  , 2 + pp (dW + 2) (dC - 2) (wW + 1) (wC - 1) ]

/-- Peak extra qubits of one controlled modular multiplication. -/
def modMulPeakWith (P : ShorLoweringPolicy) (pp : ℕ → ℕ → ℕ → ℕ → ℕ)
    (dW dC wW wC sW sC : ℕ) : ℕ :=
  (modMulPhasePeaksWith P pp dW dC wW wC sW sC).foldr max 0

/-- Peak extra qubits of the order-finding circuit. -/
def orderFindingPeakWith (P : ShorLoweringPolicy) (pp : ℕ → ℕ → ℕ → ℕ → ℕ)
    (xW dW dC wW wC sW sC : ℕ) : ℕ :=
  max (if 0 < xW then modMulPeakWith P pp dW dC wW wC sW sC else 0) (qftPeak P xW)

/-- One multiplication, phase products lowered directly. -/
def modMulPeak (P : ShorLoweringPolicy) (dW wW sW : ℕ) : ℕ :=
  modMulPeakWith P (ppPeak P) dW 0 wW 0 sW 0

/-- The order-finding circuit, phase products lowered directly. -/
def orderFindingPeak (P : ShorLoweringPolicy) (xW dW wW sW : ℕ) : ℕ :=
  orderFindingPeakWith P (ppPeak P) xW dW 0 wW 0 sW 0

/-- Peak extra qubits of a balanced split (`Balanced.splitGate`): each block
extends itself and the small operand to its common width and runs one product
there. -/
def splitPeakOf (pp : ℕ → ℕ → ℕ) : List Balanced.Block → ℕ → ℕ → ℕ → ℕ
  | [], t, wx, wz => (t - wx) + (t - wz) + pp t t
  | b :: bs, t, wx, wz =>
      max ((b.t - b.w) + (b.t - wz) + pp b.t b.t) (splitPeakOf pp bs t (wx - b.w) wz)

/-- `Balanced.fitsB` on widths and capacities. -/
def planFits (P : ShorLoweringPolicy) :
    List Balanced.Block → ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | [], t, wx, cx, wz, cz =>
      decide (wx ≤ t) && decide (wz ≤ t) &&
      decide ((t - wx) + (Policy.reserveNeed P t t).1 ≤ cx) &&
      decide ((t - wz) + (Policy.reserveNeed P t t).2 ≤ cz)
  | b :: bs, t, wx, cx, wz, cz =>
      decide (b.w < wx) && decide (b.w + 1 ≤ b.t) && decide (wz ≤ b.t) &&
      decide ((b.t - b.w) + (Policy.reserveNeed P b.t b.t).1 ≤ cx) &&
      decide ((b.t - wz) + (Policy.reserveNeed P b.t b.t).2 ≤ cz) &&
      planFits P bs t (wx - b.w) cx wz cz

/-- Peak extra qubits of a balanced phase-product site (`Balanced.siteGate`):
the split when the rule's plan fits the capacities, the product otherwise. -/
def sitePeak (P : ShorLoweringPolicy) (R : Balanced.Rule) (wx cx wz cz : ℕ) : ℕ :=
  if wz < wx then
    match R.plan wx wz with
    | some p =>
        if planFits P p.lower p.top wx cx wz cz then
          splitPeakOf (peakReserve P) p.lower p.top wx wz
        else peakReserve P wx wz
    | none => peakReserve P wx wz
  else if wx < wz then
    match R.plan wz wx with
    | some p =>
        if planFits P p.lower p.top wz cz wx cx then
          splitPeakOf (peakReserve P) p.lower p.top wz wx
        else peakReserve P wx wz
    | none => peakReserve P wx wz
  else peakReserve P wx wz

/-- `Policy.OrderFindingPeakFormula` with the budgets of this file. -/
def OrderFindingPeakFormula (P : ShorLoweringPolicy) : Prop :=
  P.Admissible →
  ∀ (a N : ℕ) (x y work scratch : ExtReg) (flag : ℕ)
    (hmod : ModMulCircuitWorkspaceOK y work)
    (hstep4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : Policy.GateWorkspaceOK P (orderFindingApprox a N x y work scratch flag hmod hstep4)),
    OrderFindingSpaceLayout x y work scratch flag →
    (orderFindingApproxLow P a N x y work scratch flag hmod hstep4 hws).peakQubits
        (orderFindingBaseSet x y work scratch flag)
      = x.width + (y.width + 1) + work.width + scratch.width + 1
        + orderFindingPeak P x.width y.width work.width scratch.width

/-- `Policy.ReferencePeakFormula` with the budgets of this file. -/
def ReferencePeakFormula (P : ShorLoweringPolicy) : Prop :=
  P.Admissible →
  ∀ (inst : ShorOrderFindingInstance) (m : ℕ),
    let layout := Reference.allocateReferenceLayout P inst m
    let xW := Reference.referenceXWidth inst
    let dW := Reference.referenceDataWidth inst
    let wW := Reference.referenceWorkWidth inst m
    let sW := Reference.referenceScratchWidth inst m
    (Reference.referenceShorCircuit P inst m).peakQubits
        (orderFindingBaseSet layout.x layout.data layout.work layout.scratch layout.flag)
      = xW + (dW + 1) + wW + sW + 1 + orderFindingPeak P xW dW wW sW

/-- `Policy.OrderFindingPeakFormulaBalanced` with the budgets of this file. -/
def OrderFindingPeakFormulaBalanced (P : ShorLoweringPolicy) (R : Balanced.Rule) : Prop :=
  P.Admissible →
  ∀ (a N : ℕ) (x y work scratch : ExtReg) (flag : ℕ)
    (hmod : ModMulCircuitWorkspaceOK y work)
    (hstep4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : Policy.GateWorkspaceOK P (orderFindingApprox a N x y work scratch flag hmod hstep4)),
    OrderFindingSpaceLayout x y work scratch flag →
    (Balanced.orderFindingApproxLowBalanced P R a N x y work scratch flag hmod hstep4 hws).peakQubits
        (orderFindingBaseSet x y work scratch flag)
      = x.width + (y.width + 1) + work.width + scratch.width + 1
        + orderFindingPeakWith P (sitePeak P R) x.width
            y.width y.capacity work.width work.capacity scratch.width scratch.capacity

end Rec
end QubitCount
end Shor
