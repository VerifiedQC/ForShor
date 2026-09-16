import Lean.Data.Json
import FastMultiplication.ShorVerification.Framework.Gatecount.ResourceModel
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Core.Language

/-!
# Common JSON printers

One printer each for the small value types shared across the emitter:
rationals, angles, registers, points, and `Prog` ops. No file outside this one
declares any of these spellings (README design principle 5).
-/

namespace Shor

open Lean (Json)

/-- A plain rational as an exact `num/den` pair (no `unit` field — contrast
`angleJson`, which is a rational multiple of `π`). -/
def ratJson (r : ℚ) : Json :=
  Json.mkObj [
    ("num", (r.num : Json)),
    ("den", (r.den : Json))
  ]

/-- An `Angle` (a rational multiple of `π`) as an exact `num/den` pair. -/
def angleJson (a : Angle) : Json :=
  Json.mkObj [
    ("num", (a.num : Json)),
    ("den", (a.den : Json)),
    ("unit", Json.str "pi")
  ]

/-- Ordered physical qubit indices of a register, LSB-first. -/
def regJson (r : Reg) : Json :=
  Json.arr (r.qubits.map (fun q => (q : Json))).toArray

/-- An extendable register as its active and reserve qubit lists. -/
def extRegJson (r : ExtReg) : Json :=
  Json.mkObj [
    ("active", regJson r.active),
    ("reserve", regJson r.reserve)
  ]

/-- A Toom-Cook interpolation point: an integer point or a `1/m`-coordinate
point (`m = 0` is the point at infinity). -/
def pointJson : Operations.Point → Json
  | .int z => Json.mkObj [("kind", Json.str "int"), ("z", (z : Json))]
  | .frac m => Json.mkObj [("kind", Json.str "frac"), ("m", (m : Json))]

/-- One op of a Toom-Cook `Prog k`. -/
def validOpJson {k : ℕ} : Operations.valid_ops k → Json
  | .shiftL i n =>
      Json.mkObj [("op", Json.str "shiftL"), ("i", ((i : ℕ) : Json)), ("n", (n : Json))]
  | .shiftR i n =>
      Json.mkObj [("op", Json.str "shiftR"), ("i", ((i : ℕ) : Json)), ("n", (n : Json))]
  | .negate i =>
      Json.mkObj [("op", Json.str "negate"), ("i", ((i : ℕ) : Json))]
  | .addScaled dst src negSrc shift =>
      Json.mkObj [
        ("op", Json.str "addScaled"),
        ("dst", ((dst : ℕ) : Json)), ("src", ((src : ℕ) : Json)),
        ("negSrc", Json.bool negSrc), ("shift", (shift : Json))
      ]
  | .phaseProduct i =>
      Json.mkObj [("op", Json.str "phaseProduct"), ("i", ((i : ℕ) : Json))]

/-- A `Prog k`, printed as its op list in order. -/
def progJson {k : ℕ} (ops : Prog k) : Json :=
  Json.arr (ops.map validOpJson).toArray

/-- Logical elementary-gate resources (`h, x, cnot, toffoli, rz, cleanAnc`). -/
def gateResourcesJson (r : GateResources) : Json :=
  Json.mkObj [
    ("h", (r.h : Json)),
    ("x", (r.x : Json)),
    ("cnot", (r.cnot : Json)),
    ("toffoli", (r.toffoli : Json)),
    ("rz", (r.rz : Json)),
    ("cleanAnc", (r.cleanAnc : Json))
  ]

end Shor
