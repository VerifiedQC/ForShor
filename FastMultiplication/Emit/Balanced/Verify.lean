import FastMultiplication.Emit.Balanced.Templates
import FastMultiplication.Emit.Reflect.PolicyVerify
import FastMultiplication.ShorVerification.Implementation.Reference.Balanced.Reference

/-!
# Balanced IR: agreement with the real balanced lowering, at sampled widths

The same evaluation tier as `Reflect/PolicyVerify.lean`, for the two balanced site
templates and the retargeted `shor`:

* **full depth** (`checkBalancedSiteAt`): `instantiate (balanceDoc doc) "balanced_(c)phase_product"`
  at concrete unequal registers equals `Policy.lowerGate P (siteGate P defaultRule c φ x z) _`,
  ForShor's own lowering of the balanced site, at small width pairs (padding, two- and
  three-block, both orientations, equal widths), in two reserve regimes;
* **one level at n = 2048** (`checkBalancedSiteShallowAt`): at the four Shor site shapes of the
  n = 2048 reference run, with reserves exactly the original site's `Policy.reserveNeed`, one level
  of the template (dispatcher calls shallow, as in the band-body check) equals the high-level gate
  `siteGate P defaultRule c φ x z`, AND that gate is the split (not the fallback);
* **`shor`** (`checkBalancedShorAt`): `instantiate (balanceDoc doc) "shor"` equals
  `Balanced.balancedShorCircuit P defaultRule inst m` at the reference instances.

Evaluation, not a theorem.
-/

namespace Shor
namespace Reflect
namespace Balanced

open IR IR.Balanced Shor.Balanced

/-- Registers `x` (width `xw`), `z` (width `zw`) and a control, with reserves
`reserveNeed P xw zw + extra`. -/
def rectRegisters (P : ShorLoweringPolicy) (xw zw extra : ℕ) :
    Except String (ExtReg × ExtReg × ℕ) :=
  let need := Policy.reserveNeed P xw zw
  let xActive := Reg.interval 0 xw
  let xReserve := Reg.interval xw (need.1 + extra)
  if hx : Disjoint xActive xReserve then
    let zStart := xw + (need.1 + extra)
    let zActive := Reg.interval zStart zw
    let zReserve := Reg.interval (zStart + zw) (need.2 + extra)
    if hz : Disjoint zActive zReserve then
      .ok (ExtReg.withReserve xActive xReserve hx, ExtReg.withReserve zActive zReserve hz,
        zStart + zw + (need.2 + extra))
    else .error "internal: z active/reserve overlap"
  else .error "internal: x active/reserve overlap"

def siteEnv (s : ShorPolicySubmission) (x z : ExtReg) (ctrl : ℕ) (phi : Angle)
    (leaf : String → List ℕ → List Angle → List ExtReg → Option (Except String Gate) :=
      fun _ _ _ _ => none) : Env :=
  { w := fun name =>
      if name == "xw" then some x.width
      else if name == "zw" then some z.width
      else if name == "xCap" then some x.capacity
      else if name == "zCap" then some z.capacity
      else none
    a := fun name => if name == "phi" then some phi else none
    r := fun name =>
      if name == "ctrl" then some (ExtReg.ofReg (Reg.interval ctrl 1))
      else if name == "x" then some x else if name == "z" then some z else none
    opaqueW := policyOpaqueDispatch s.policy
    coeff := policyCoeffDispatch s
    leafCall := leaf }

/-- Full-depth agreement of one balanced site template with ForShor's lowering of `siteGate`. -/
def checkBalancedSiteAt (s : ShorPolicySubmission) (doc : Doc) (controlled : Bool)
    (xw zw extra : ℕ) : Except String Unit := do
  let (x, z, ctrl) ← rectRegisters s.policy xw zw extra
  let phi : Angle := (1 : ℚ) / 4
  let c : Ctl := if controlled then .ctrl ctrl else .none
  let env := siteEnv s x z ctrl phi
  let g ← instantiate (balanceDoc doc) (balancedName controlled) env policyFuel
  let real ← (if controlled then
      if h : Policy.CWorkspaceOK s.policy ctrl x z then
        .ok (Policy.lowerGate s.policy (siteGate s.policy defaultRule (.ctrl ctrl) phi x z)
          (siteGate_ok s.policy defaultRule (.ctrl ctrl) phi x z h))
      else .error "insufficient workspace"
    else
      if h : Policy.WorkspaceOK s.policy x z then
        .ok (Policy.lowerGate s.policy (siteGate s.policy defaultRule .none phi x z)
          (siteGate_ok s.policy defaultRule .none phi x z h))
      else .error "insufficient workspace" : Except String LowGate)
  let _ := c
  if lowGateAgrees g real then .ok ()
  else .error s!"balanced site (controlled={controlled}) disagrees at ({xw}, {zw}), extra={extra}"

/-- One level of a balanced site template at given registers, against `siteGate`;
returns whether the split branch was taken. -/
def checkBalancedSiteShallowAt (s : ShorPolicySubmission) (doc : Doc) (controlled : Bool)
    (xw zw extra : ℕ) : Except String Bool := do
  let (x, z, ctrl) ← rectRegisters s.policy xw zw extra
  let phi : Angle := (1 : ℚ) / 4
  let c : Ctl := if controlled then .ctrl ctrl else .none
  let env := siteEnv s x z ctrl phi (shallowLeafCall controlled)
  let g ← instantiateGate (balanceDoc doc) (balancedName controlled) env policyFuel
  let real := siteGate s.policy defaultRule c phi x z
  if gateAgrees g real then .ok (!gateAgrees real (c.gate phi x z))
  else .error s!"balanced site, one level (controlled={controlled}), disagrees at ({xw}, {zw})"

/-- `shor` of the balanced document against the balanced reference circuit. -/
def checkBalancedShorAt (s : ShorPolicySubmission) (inst : ShorOrderFindingInstance) (m : ℕ)
    (doc : Doc) : Except String Unit :=
  let layout := Reference.allocateReferenceLayout s.policy inst m
  let real := balancedShorCircuit s.policy defaultRule inst m
  match instantiate (balanceDoc doc) "shor" (policyShorEnv s inst layout) 400 with
  | .error e => .error s!"balanced shor: instantiate: {e}"
  | .ok g =>
      if lowGateAgrees g real then .ok ()
      else .error s!"balanced shor: disagrees at N={inst.N}, m={m}"

/-- Full-depth width pairs: padding, two and three blocks, both orientations, equal widths,
degenerate small widths. -/
def fullDepthPairs : List (ℕ × ℕ) :=
  [(12, 9), (9, 12), (20, 9), (9, 20), (30, 17), (17, 30), (50, 17), (17, 50), (45, 30),
   (15, 4), (4, 15), (3, 2), (2, 3), (16, 16)]

/-- The reserve regimes: exactly the original site's need, and generous. -/
def extras : List ℕ := [0, 64, 256]

/-- The four Shor site shapes at n = 2048 (data = 2048, work = 2347, scratch = 4398), with
whether the site is controlled. -/
def sites2048 : List (Bool × ℕ × ℕ) :=
  [(true, 2049, 2348), (false, 2348, 2050), (false, 2348, 4399), (true, 2050, 2348)]

/-- Whether `siteGate` takes the split at registers `(xw, zw, extra)` (not the fallback). -/
def splitTakenAt (s : ShorPolicySubmission) (xw zw extra : ℕ) : Bool :=
  match rectRegisters s.policy xw zw extra with
  | .ok (x, z, _) =>
      !gateAgrees (siteGate s.policy defaultRule .none ((1 : ℚ) / 4) x z)
        (Gate.SignedPhaseProd ((1 : ℚ) / 4) x z)
  | .error _ => false

/-- Non-vacuity: at slack 256 every unequal pair with `min ≥ 2` really is split, so the
full-depth comparisons exercise the balanced branch, not only the fallback. -/
def nonVacuous (s : ShorPolicySubmission) : Bool :=
  fullDepthPairs.all fun p =>
    if p.1 == p.2 || min p.1 p.2 < 2 then true else splitTakenAt s p.1 p.2 256

/-- The balanced tier as one `Bool`, plus the per-site split record at n = 2048. -/
def balancedChecks (s : ShorPolicySubmission) (doc : Doc) : Bool × List (Bool × ℕ × ℕ × Bool) :=
  let full := fullDepthPairs.all fun p => extras.all fun e =>
    okB (checkBalancedSiteAt s doc false p.1 p.2 e) && okB (checkBalancedSiteAt s doc true p.1 p.2 e)
  let shor := submissionShorInstances.all fun im => okB (checkBalancedShorAt s im.1 im.2 doc)
  let shallow := sites2048.map fun st =>
    match checkBalancedSiteShallowAt s doc st.1 st.2.1 st.2.2 0 with
    | .ok split => (true, st.2.1, st.2.2, split)
    | .error _ => (false, st.2.1, st.2.2, false)
  (full && nonVacuous s && shor && shallow.all (fun r => r.1 && r.2.2.2) && (balanceDoc doc).wellFormed, shallow)

end Balanced
end Reflect
end Shor
