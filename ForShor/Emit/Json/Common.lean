import Lean.Data.Json
import ForShor.ShorVerification.Framework.Gatecount.ResourceModel
import ForShor.ShorVerification.Implementation.PhaseProduct.Proofs.Math.Table_Generation.Core.Language

/-!
# Common JSON printers

One printer each for the small value types shared across the emitter:
rationals, angles, registers, points, and `Prog` ops. No file outside this one
declares any of these spellings.
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

/-- A `NegationMethod`'s spelling in every document: its constructor name, `"oneQubit"` (the default) or
`"scratch"`. -/
def negationMethodStr : NegationMethod → String
  | .oneQubit => "oneQubit"
  | .scratch => "scratch"

/-- The `"negation"` field: which method the document's resource figures are priced under. -/
def negationMethodJson (m : NegationMethod) : Json := Json.str (negationMethodStr m)

/-- A `w`-bit register with no reserve, only so that a negation's charge can be read off at a width. -/
def negationProbeReg (w : ℕ) : ExtReg := ExtReg.ofReg ⟨List.range w, List.nodup_range⟩

/-- The charge of one `Negate` of a `w`-bit register under the method `m`, as `ResourceModel` states it
(`negateResourcesFor`). -/
def negateChargeAt (m : NegationMethod) (w : ℕ) : GateResources :=
  negateResourcesFor m (negationProbeReg w)

/-- Widths at which `negateChargeJson` evaluates the charge: two small even and odd ones and the 2048-bit
benchmark's. -/
def negateChargeWidths : List ℕ := [8, 9, 2048]

/-- The per-method charge of a `Negate`, for a consumer that prices the circuit itself: the method, the
closed forms (their range of validity is in each `note`), and the charge evaluated at `negateChargeWidths`. The
elementary-gate counts of the circuit's other gates do not depend on the method. -/
def negateChargeJson (m : NegationMethod) : Json :=
  let formulas : Json :=
    match m with
    | .oneQubit => Json.mkObj [
        ("clean_ancilla", Json.str "1"),
        ("x", Json.str "w even: 5w-3, w odd: 5w+1"),
        ("cnot", Json.str "w even: 17w-22, w odd: 17w-5"),
        ("toffoli", Json.str "w even: 12w-28, w odd: 10w-18"),
        ("note", Json.str "complement, then Gidney's one-ancilla increment; exact for w >= 7")]
    | .scratch => Json.mkObj [
        ("clean_ancilla", Json.str "w+1"),
        ("x", Json.str "3w-4"),
        ("cnot", Json.str "5w-7"),
        ("toffoli", Json.str "2w-3"),
        ("note", Json.str "complement, then a Cuccaro modulo adder against a clean constant-one register; \
          the published adder formula, w >= 3")]
  Json.mkObj [
    ("method", negationMethodJson m),
    ("formulas", formulas),
    ("at_width", Json.mkObj (negateChargeWidths.map fun w =>
      (toString w, gateResourcesJson (negateChargeAt m w))))]

end Shor
