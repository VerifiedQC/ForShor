import FastMultiplication.Emit.Table.Source
import FastMultiplication.ShorVerification.Framework.Gatecount.ResourceModel
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Gates.NaiveLeaf

/-!
# E1: op census and per-op-class `LowGate` resources

Counts of each `Prog k` op, the adder-class total, and the `LowGate` resources
this repository assigns to each op class at a chosen width `W` — read
directly off `Framework/Gatecount/ResourceModel.lean`'s `addScaledResources`,
`negateResources`, `radixReverseResources`, and off the real gate census of
`LowGate.Naive_SignedPhaseProd` at operand widths `(wx, wz)`.
-/

namespace Shor

open Operations

/-- Counts of each `Prog k` op class. -/
structure OpCensus where
  phaseProduct : ℕ
  addScaled : ℕ
  negate : ℕ
  shiftL : ℕ
  shiftR : ℕ
deriving Repr

/-- Combined adder-class total, `A_k` in the README's notation. -/
def OpCensus.adderClassTotal (c : OpCensus) : ℕ := c.addScaled + c.negate

/-- Census a `Prog k`. -/
def opCensus {k : ℕ} (ops : Prog k) : OpCensus :=
  ops.foldl
    (fun c op =>
      match op with
      | .phaseProduct _ => { c with phaseProduct := c.phaseProduct + 1 }
      | .addScaled .. => { c with addScaled := c.addScaled + 1 }
      | .negate _ => { c with negate := c.negate + 1 }
      | .shiftL .. => { c with shiftL := c.shiftL + 1 }
      | .shiftR .. => { c with shiftR := c.shiftR + 1 })
    { phaseProduct := 0, addScaled := 0, negate := 0, shiftL := 0, shiftR := 0 }

/-- A width-only synthetic register, used to evaluate width-indexed resource
functions at a chosen width without reference to a real layout (mirrors the
`widthShell` pattern in `Reference/ReferenceLayout.lean`; that one is
`private`, so this is its own copy for the emitter). -/
def synthReg (n : ℕ) : ExtReg := ExtReg.ofReg (Reg.interval 0 n)

@[simp] theorem width_synthReg (n : ℕ) : (synthReg n).width = n := by
  simp [synthReg, ExtReg.ofReg, ExtReg.width, Reg.interval, Reg.width, regSize]

/-- `addScaledResources` at width `W` (sign/shift don't affect the count). -/
def addScaledResourcesAt (W : ℕ) : GateResources :=
  addScaledResources (synthReg W) (synthReg W) false 0

/-- `negateResources` at width `W`. -/
def negateResourcesAt (W : ℕ) : GateResources :=
  negateResources (synthReg W)

/-- `radixReverseResources` at width `W`. -/
def radixReverseResourcesAt (W : ℕ) : GateResources :=
  radixReverseResources (Reg.interval 0 W) W

/-- Exact gate census of `Naive_SignedPhaseProd` at operand widths `(wx, wz)`,
counted on the real term (the angle doesn't affect gate counts). -/
def naiveLeafResourcesAt (wx wz : ℕ) : GateResources :=
  LowGate.resources shorGateResourceModel
    (LowGate.Naive_SignedPhaseProd 0 (synthReg wx) (synthReg wz))

end Shor
