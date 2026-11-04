import ForShor.Emit.BalancedU.Templates
import ForShor.Emit.Balanced.Verify
import ForShor.ShorVerification.Implementation.Reference.Balanced.Unconditional

/-!
# Unconditionally balanced IR: agreement with the real lowering, at sampled widths

The evaluation tier of `Emit/Balanced/Verify.lean`, for the two unconditional site templates
and the retargeted `shor`. Registers carry the reserve the reference layout gives a site,
`Reference.referenceSiteReserve` (the product's `reserveNeed` and the default rule's block need,
whichever is larger), plus a slack:

* **full depth** (`checkBalancedUSiteAt`): `instantiate (balanceUDoc doc) "balanced_u_(c)phase_product"`
  equals `Policy.lowerGate P (siteGateU defaultRule c φ x z) _`, at the width pairs of the
  balanced tier, in three slack regimes;
* **against the conditional templates** (`checkAgreesWithBalancedAt`): on the same registers the
  conditional and the unconditional templates instantiate to the same circuit (there `fitsB`
  holds, so `siteGate` and `siteGateU` coincide);
* **one level at n = 2048** (`checkBalancedUSiteShallowAt`): at the four Shor site shapes of the
  n = 2048 reference run, one level of the template (dispatcher calls shallow) equals the
  high-level gate `siteGateU defaultRule c φ x z`, AND that gate is the split: with the
  reference layout's reserves, with only the original site's `Policy.reserveNeed`, and with
  reserves covering only the extensions, where `fitsB` fails;
* **`shor`** (`checkBalancedUShorAt`): `instantiate (balanceUDoc doc) "shor"` equals
  `Balanced.balancedUShorCircuit P defaultRule inst m` at the reference instances.

Evaluation, not a theorem.
-/

namespace Shor
namespace Reflect
namespace BalancedU

open IR IR.Balanced IR.BalancedU Shor.Balanced Reflect.Balanced

/-- Registers `x` (width `xw`, reserve `xr`), `z` (width `zw`, reserve `zr`) and a control. -/
def registersWith (xw zw xr zr : ℕ) : Except String (ExtReg × ExtReg × ℕ) :=
  let xActive := Reg.interval 0 xw
  let xReserve := Reg.interval xw xr
  if hx : Disjoint xActive xReserve then
    let zStart := xw + xr
    let zActive := Reg.interval zStart zw
    let zReserve := Reg.interval (zStart + zw) zr
    if hz : Disjoint zActive zReserve then
      .ok (ExtReg.withReserve xActive xReserve hx, ExtReg.withReserve zActive zReserve hz,
        zStart + zw + zr)
    else .error "internal: z active/reserve overlap"
  else .error "internal: x active/reserve overlap"

/-- Registers with reserves `referenceSiteReserve P xw zw + extra`. -/
def siteRegisters (P : ShorLoweringPolicy) (xw zw extra : ℕ) :
    Except String (ExtReg × ExtReg × ℕ) :=
  let need := Reference.referenceSiteReserve P xw zw
  registersWith xw zw (need.1 + extra) (need.2 + extra)

/-- The policy with no band: every product is the leaf, whose `reserveNeed` is zero. -/
def leafPolicy : ShorLoweringPolicy := { bands := [], sorted := by simp }

/-- Registers whose reserves are exactly the extensions the default rule's plan makes (its
`siteNeed` under `leafPolicy`) and nothing for the block products: `fitsB` fails wherever a
block product needs reserve. -/
def extensionRegisters (xw zw : ℕ) : Except String (ExtReg × ExtReg × ℕ) :=
  let e := siteNeed leafPolicy defaultRule xw zw
  registersWith xw zw e.1 e.2

private instance ctlOKDecidable (P : ShorLoweringPolicy) :
    (c : Ctl) → (x z : ExtReg) → Decidable (c.OK P x z)
  | .none, x, z => inferInstanceAs (Decidable (Policy.WorkspaceOK P x z))
  | .ctrl q, x, z => inferInstanceAs (Decidable (Policy.CWorkspaceOK P q x z))

/-- ForShor's lowering of `siteGateU defaultRule c φ x z`, on registers holding the default
rule's `siteNeed`. -/
def lowerSiteU (P : ShorLoweringPolicy) (c : Ctl) (φ : Angle) (x z : ExtReg) :
    Except String LowGate :=
  if hx : (siteNeed P defaultRule x.width z.width).1 ≤ x.capacity then
    if hz : (siteNeed P defaultRule x.width z.width).2 ≤ z.capacity then
      if h : c.OK P x z then
        .ok (Policy.lowerGate P (siteGateU defaultRule c φ x z) (by
          rw [siteGateU_eq c φ (siteFits_of_siteNeed P hx hz)]
          exact siteGate_ok P defaultRule c φ x z h))
      else .error "insufficient workspace"
    else .error "z reserve below the plan's need"
  else .error "x reserve below the plan's need"

/-- Full-depth agreement of one unconditional site template with ForShor's lowering of
`siteGateU`. -/
def checkBalancedUSiteAt (s : ShorPolicySubmission) (doc : Doc) (controlled : Bool)
    (xw zw extra : ℕ) : Except String Unit := do
  let (x, z, ctrl) ← siteRegisters s.policy xw zw extra
  let phi : Angle := (1 : ℚ) / 4
  let c : Ctl := if controlled then .ctrl ctrl else .none
  let g ← instantiate (balanceUDoc doc) (balancedUName controlled) (siteEnv s x z ctrl phi) policyFuel
  let real ← lowerSiteU s.policy c phi x z
  if lowGateAgrees g real then .ok ()
  else .error s!"unconditional site (controlled={controlled}) disagrees at ({xw}, {zw}), extra={extra}"

/-- On registers where `fitsB` holds, the conditional and the unconditional site templates
instantiate to the same circuit. -/
def checkAgreesWithBalancedAt (s : ShorPolicySubmission) (doc : Doc) (controlled : Bool)
    (xw zw extra : ℕ) : Except String Unit := do
  let (x, z, ctrl) ← siteRegisters s.policy xw zw extra
  let env := siteEnv s x z ctrl ((1 : ℚ) / 4)
  let gU ← instantiate (balanceUDoc doc) (balancedUName controlled) env policyFuel
  let gB ← instantiate (balanceDoc doc) (balancedName controlled) env policyFuel
  if lowGateAgrees gU gB then .ok ()
  else .error s!"unconditional and conditional sites differ at ({xw}, {zw}), extra={extra}"

/-- One level of an unconditional site template at given registers, against `siteGateU`;
returns whether the split branch was taken. -/
def checkBalancedUSiteShallowAt (s : ShorPolicySubmission) (doc : Doc) (controlled : Bool)
    (x z : ExtReg) (ctrl : ℕ) : Except String Bool := do
  let phi : Angle := (1 : ℚ) / 4
  let c : Ctl := if controlled then .ctrl ctrl else .none
  let env := siteEnv s x z ctrl phi (shallowLeafCall controlled)
  let g ← instantiateGate (balanceUDoc doc) (balancedUName controlled) env policyFuel
  let real := siteGateU defaultRule c phi x z
  if gateAgrees g real then .ok (!gateAgrees real (c.gate phi x z))
  else .error s!"unconditional site, one level (controlled={controlled}), disagrees at \
    ({x.width}, {z.width})"

/-- `shor` of the unconditional document against the unconditionally balanced reference circuit. -/
def checkBalancedUShorAt (s : ShorPolicySubmission) (inst : ShorOrderFindingInstance) (m : ℕ)
    (doc : Doc) : Except String Unit :=
  let layout := Reference.allocateReferenceLayout s.policy inst m
  let real := balancedUShorCircuit s.policy defaultRule inst m (reference_fits s.policy inst m)
  match instantiate (balanceUDoc doc) "shor" (policyShorEnv s inst layout) 400 with
  | .error e => .error s!"unconditional shor: instantiate: {e}"
  | .ok g =>
      if lowGateAgrees g real then .ok ()
      else .error s!"unconditional shor: disagrees at N={inst.N}, m={m}"

/-- Whether `siteGateU` takes the split at registers `(xw, zw, extra)` (not the original site). -/
def splitTakenAtU (s : ShorPolicySubmission) (xw zw extra : ℕ) : Bool :=
  match siteRegisters s.policy xw zw extra with
  | .ok (x, z, _) =>
      !gateAgrees (siteGateU defaultRule .none ((1 : ℚ) / 4) x z)
        (Gate.SignedPhaseProd ((1 : ℚ) / 4) x z)
  | .error _ => false

/-- Non-vacuity: with no slack every unequal pair with `min ≥ 2` really is split, so the
full-depth comparisons exercise the split, not only the original site. -/
def nonVacuousU (s : ShorPolicySubmission) : Bool :=
  fullDepthPairs.all fun p =>
    if p.1 == p.2 || min p.1 p.2 < 2 then true else splitTakenAtU s p.1 p.2 0

/-- One level at an n = 2048 site in three reserve regimes: `(agrees, xw, zw, split with the
reference layout's reserves, split with only the original site's reserves, split with reserves
covering only the extensions)`. The last regime is where `fitsB` fails, so a template that
still checked it would fall back there and disagree with `siteGateU`. -/
def site2048 (s : ShorPolicySubmission) (doc : Doc) (st : Bool × ℕ × ℕ) :
    Bool × ℕ × ℕ × Bool × Bool × Bool :=
  let shallow (r : Except String (ExtReg × ExtReg × ℕ)) : Except String Bool := do
    let (x, z, ctrl) ← r
    checkBalancedUSiteShallowAt s doc st.1 x z ctrl
  match shallow (siteRegisters s.policy st.2.1 st.2.2 0),
      shallow (rectRegisters s.policy st.2.1 st.2.2 0),
      shallow (extensionRegisters st.2.1 st.2.2) with
  | .ok a, .ok b, .ok c => (true, st.2.1, st.2.2, a, b, c)
  | _, _, _ => (false, st.2.1, st.2.2, false, false, false)

/-- The unconditional tier as one `Bool`, plus the per-site split record at n = 2048. -/
def balancedUChecks (s : ShorPolicySubmission) (doc : Doc) :
    Bool × List (Bool × ℕ × ℕ × Bool × Bool × Bool) :=
  let full := fullDepthPairs.all fun p => extras.all fun e =>
    okB (checkBalancedUSiteAt s doc false p.1 p.2 e) && okB (checkBalancedUSiteAt s doc true p.1 p.2 e)
  let agree := fullDepthPairs.all fun p =>
    okB (checkAgreesWithBalancedAt s doc false p.1 p.2 0) &&
      okB (checkAgreesWithBalancedAt s doc true p.1 p.2 0)
  let shor := submissionShorInstances.all fun im => okB (checkBalancedUShorAt s im.1 im.2 doc)
  let sites := sites2048.map (site2048 s doc)
  (full && agree && nonVacuousU s && shor && sites.all (fun r => r.1 && r.2.2.2.1 && r.2.2.2.2.1 && r.2.2.2.2.2) &&
    (balanceUDoc doc).wellFormed, sites)

end BalancedU
end Reflect
end Shor
