import FastMultiplication.Emit.Reflect.Verify
import FastMultiplication.Emit.Symbolic.Dispatcher

/-!
# The evaluation tier for a policy document

`Verify.lean` instantiates a single-table document and compares it against
the real compiled circuit at sampled widths. This file does the same for a
policy document, against `Policy.lowerSignedPhaseProd` and friends.

Two things are worth stating plainly, because they are what the tier does
and does not buy.

**What it checks.** Instantiating the entry template `phase_product` — which
in a policy document is the *dispatcher* — exercises the guard chain, the
band body it routes to, and the recursion back through the dispatcher, all
in one. So a single width check covers every layer the recursion from that
width passes through.
`policySubmissionChecks` checks the dispatchers exactly against the proved
template and samples the bodies on the *probe submission* at widths that
depend only on the tables (see the section at the end of this file); the
band boundaries need no sampling, since the dispatcher's routing is a
theorem.

**What it does not.** This is evaluation at sampled widths, not a theorem,
exactly as for a single table. The one thing that *is* proved is that the
emitted guard chain agrees with `ShorLoweringPolicy.choose` at every width —
`IR.dispatcherCallAt_dispatcherTemplate` — so the band a width is routed to
is never in question; what is sampled is whether each band's body matches
the circuit.

## The oracles

The width oracles need no new names and no new arities. `Policy.reserveNeed
P` is already a function of `(wx, wz)` alone, and `nextWidth` is evaluated
by a band body only at widths the dispatcher sent there, where the
policy-keyed and band-keyed answers agree. So `policyOpaqueDispatch` has
exactly `opaqueDispatch`'s signature.

The *coefficient* oracle is the one place a policy really does need more
than a table does, and `Registry.coeffOffset` is how it gets it: band `i`'s
point indices are shifted by `Σ_{j<i} q kⱼ`, so one oracle resolves indices
into the bands' point lists concatenated. Without that, two bands with
different `k` would both emit `coeff 0`, `coeff 1`, … meaning different
numbers.
-/

namespace Shor.Reflect

open Shor.IR Operations

/-! ## Policy-keyed oracles -/

/-- `nextWidth` under a policy, as a total function of the operand widths:
the chosen table's `nextWidth`, or no step at all below the last threshold.

Total because the IR's opaque functions are, and single-valued because
`choose` is. A band body evaluates it only at widths inside its own band,
where it coincides with that band's own table's `nextWidth`. -/
def policyNextWidth (P : ShorLoweringPolicy) (wx wz : ℕ) : ℕ :=
  match P.choose (max wx wz) with
  | some T => RecursivePhaseWorkspace.nextWidthBy P.widthRule T.ops wx wz
  | none => max wx wz

/-- `opaqueDispatch`, keyed on a policy. Same names, same arities: a policy
document publishes no new oracle. -/
def policyOpaqueDispatch (P : ShorLoweringPolicy) : String → List ℕ → Option ℕ :=
  fun name args =>
    match name, args with
    | "nextWidth", [xw, zw] => some (policyNextWidth P xw zw)
    | "reserveNeed_x", [xw, zw] => some (Policy.reserveNeed P xw zw).1
    | "reserveNeed_z", [xw, zw] => some (Policy.reserveNeed P xw zw).2
    | "qftXWork", [w] => some (Policy.qftWorkspaceNeed P w).1
    | "qftZWork", [w] => some (Policy.qftWorkspaceNeed P w).2
    | "log2", [n] => some (Nat.log2 n)
    | "mod", [m, n] => some (m % n)
    | "pow", [b, e] => some (b ^ e)
    | "modpow", [b, e, n] => some ((b ^ (2 ^ e)) % n)
    | "step5Const", [c, n] => some (step5Constant c n)
    | _, _ => none

/-- Resolve a concatenated point index against the bands in order, peeling
`q kⱼ` indices per band — the decoding of `Registry.coeffOffset`. -/
def policyCoeffFrom : List (ℕ × ShorLoweringSetup) → ℕ → ℕ → Option ℚ
  | [], _, _ => none
  | b :: bs, l, mv =>
      if h : l < q b.2.k then
        some (cramerCoeffFromPtsWidth b.2.k mv b.2.pts b.2.hpts ⟨l, h⟩)
      else policyCoeffFrom bs (l - q b.2.k) mv

/-- The `coeff` oracle for a policy document. -/
def policyCoeffDispatch (s : ShorPolicySubmission) : ℕ → ℕ → Option ℚ :=
  fun l mv => policyCoeffFrom s.bands l mv

/-! ## Registers sized by the policy -/

/-- `ppRegisters`, with the reserve sized by `Policy.reserveNeed`. -/
def policyPPRegisters (P : ShorLoweringPolicy) (n : ℕ) (slack : ℕ := 1) :
    Except String (ExtReg × ExtReg × ℕ) :=
  let need := Policy.reserveNeed P n n
  let xActive := Reg.interval 0 n
  let xReserve := Reg.interval n (need.1 + slack)
  if hx : Disjoint xActive xReserve then
    let zStart := n + (need.1 + slack)
    let zActive := Reg.interval zStart n
    let zReserve := Reg.interval (zStart + n) (need.2 + slack)
    if hz : Disjoint zActive zReserve then
      let ctrl := zStart + n + (need.2 + slack)
      .ok (ExtReg.withReserve xActive xReserve hx, ExtReg.withReserve zActive zReserve hz, ctrl)
    else .error "internal: z active/reserve overlap"
  else .error "internal: x active/reserve overlap"

/-- `qftRegister`, with the reserve sized by `Policy.qftWorkspaceNeed`. -/
def policyQftRegister (P : ShorLoweringPolicy) (w : ℕ) : Except String ExtReg :=
  let need := Policy.qftWorkspaceNeed P w
  let active := Reg.interval 0 w
  let reserve := Reg.interval w (need.1 + need.2)
  if h : Disjoint active reserve then .ok (ExtReg.withReserve active reserve h)
  else .error "internal: qft active/reserve overlap"

/-! ## The checks -/

/-- Unrolling budget. Larger than the single-table tier's `200` because a
policy chain alternates dispatcher and body, so each level of the real
recursion costs two template activations. -/
def policyFuel : ℕ := 600

/-- The dispatcher, instantiated at concrete registers, agrees with the real
policy-lowered circuit. -/
def policyPhaseProductAgrees (s : ShorPolicySubmission) (doc : Doc) (x z : ExtReg) (phi : Angle)
    (hws : Policy.WorkspaceOK s.policy x z) : Bool :=
  let real := Policy.lowerSignedPhaseProd s.policy phi x z hws
  let env : Env :=
    { w := fun name =>
        if name == "xw" then some x.width
        else if name == "zw" then some z.width
        else if name == "xCap" then some x.capacity
        else if name == "zCap" then some z.capacity
        else none
      a := fun name => if name == "phi" then some phi else none
      r := fun name => if name == "x" then some x else if name == "z" then some z else none
      opaqueW := policyOpaqueDispatch s.policy
      coeff := policyCoeffDispatch s }
  match instantiate doc "phase_product" env policyFuel with
  | .error _ => false
  | .ok g => lowGateAgrees g real

/-- `phase_product` agreement at one width and reserve regime. -/
def checkPolicyPhaseProductAt (s : ShorPolicySubmission) (n : ℕ) (doc : Doc) (slack : ℕ := 1) :
    Except String Unit :=
  match policyPPRegisters s.policy n slack with
  | .error e => .error s!"policy template check (phase_product): {e}"
  | .ok (x, z, _ctrl) =>
      if hws : Policy.WorkspaceOK s.policy x z then
        if policyPhaseProductAgrees s doc x z ((1 : ℚ) / 4) hws then .ok ()
        else .error
          s!"policy template check (phase_product): instantiate disagrees with the real term \
            at n={n}, slack={slack}"
      else .error
        s!"policy template check (phase_product): insufficient workspace at n={n}, slack={slack}"

/-- Controlled counterpart of `policyPhaseProductAgrees`. -/
def policyCPhaseProductAgrees (s : ShorPolicySubmission) (doc : Doc) (ctrl : ℕ)
    (x z : ExtReg) (phi : Angle) (hws : Policy.CWorkspaceOK s.policy ctrl x z) : Bool :=
  let real := Policy.lowerCSignedPhaseProd s.policy ctrl phi x z hws
  let ctrlReg := ExtReg.ofReg (Reg.interval ctrl 1)
  let env : Env :=
    { w := fun name =>
        if name == "xw" then some x.width
        else if name == "zw" then some z.width
        else if name == "xCap" then some x.capacity
        else if name == "zCap" then some z.capacity
        else none
      a := fun name => if name == "phi" then some phi else none
      r := fun name =>
        if name == "ctrl" then some ctrlReg
        else if name == "x" then some x else if name == "z" then some z else none
      opaqueW := policyOpaqueDispatch s.policy
      coeff := policyCoeffDispatch s }
  match instantiate doc "cphase_product" env policyFuel with
  | .error _ => false
  | .ok g => lowGateAgrees g real

/-- `cphase_product` agreement at one width and reserve regime. -/
def checkPolicyCPhaseProductAt (s : ShorPolicySubmission) (n : ℕ) (doc : Doc) (slack : ℕ := 1) :
    Except String Unit :=
  match policyPPRegisters s.policy n slack with
  | .error e => .error s!"policy template check (cphase_product): {e}"
  | .ok (x, z, ctrl) =>
      if hws : Policy.CWorkspaceOK s.policy ctrl x z then
        if policyCPhaseProductAgrees s doc ctrl x z ((1 : ℚ) / 4) hws then .ok ()
        else .error
          s!"policy template check (cphase_product): instantiate disagrees with the real term \
            at n={n}, slack={slack}"
      else .error
        s!"policy template check (cphase_product): insufficient workspace at n={n}, slack={slack}"

/-- `qft` agreement at one width, with the embedded phase product reaching
the dispatcher at the split's generally-unequal operand pair. -/
def checkPolicyQftAt (s : ShorPolicySubmission) (w : ℕ) (doc : Doc) : Except String Unit :=
  match policyQftRegister s.policy w with
  | .error e => .error s!"policy template check (qft): {e}"
  | .ok r =>
      if hws : Policy.QFTReserveOK s.policy r then
        let xWork := ExtReg.ofReg (Policy.qftXWork s.policy r)
        let zWork := ExtReg.ofReg (Policy.qftZWork s.policy r)
        let real := Policy.lowerQFT s.policy r hws
        let env : Env :=
          { w := fun name =>
              if name == "w" then some r.width
              else if name == "xWorkW" then some xWork.width
              else if name == "zWorkW" then some zWork.width
              else none
            a := fun _ => none
            r := fun name =>
              if name == "r" then some r
              else if name == "xWork" then some xWork
              else if name == "zWork" then some zWork
              else none
            opaqueW := policyOpaqueDispatch s.policy
            coeff := policyCoeffDispatch s }
        match instantiate doc "qft" env policyFuel with
        | .error _ => .error s!"policy template check (qft): instantiate failed at w={w}"
        | .ok g =>
            if lowGateAgrees g real then .ok ()
            else .error
              s!"policy template check (qft): instantiate disagrees with the real term at w={w}"
      else .error s!"policy template check (qft): insufficient workspace at w={w}"

/-- The `shor_gate`/`shor` environment under a policy. The reference layout
machinery already takes a policy, so only the two oracles change. -/
def policyShorEnv (s : ShorPolicySubmission) (inst : ShorOrderFindingInstance)
    (layout : Reference.ReferenceShorLayout) : Env :=
  { w := fun name =>
      if name == "a" then some inst.a
      else if name == "N" then some inst.N
      else if name == "xW" then some layout.x.width
      else if name == "xCap" then some layout.x.capacity
      else if name == "yW" then some layout.data.width
      else if name == "yCap" then some layout.data.capacity
      else if name == "workW" then some layout.work.width
      else if name == "workCap" then some layout.work.capacity
      else if name == "scratchW" then some layout.scratch.width
      else if name == "scratchCap" then some layout.scratch.capacity
      else none
    a := fun _ => none
    r := fun name =>
      if name == "x" then some layout.x
      else if name == "y" then some layout.data
      else if name == "work" then some layout.work
      else if name == "scratch" then some layout.scratch
      else if name == "flag" then some (ExtReg.ofReg (Reg.interval layout.flag 1))
      else none
    opaqueW := policyOpaqueDispatch s.policy
    coeff := policyCoeffDispatch s }

/-- `shor_gate` agreement at one reference instance and precision. -/
def checkPolicyShorGateAt (s : ShorPolicySubmission) (inst : ShorOrderFindingInstance) (m : ℕ)
    (doc : Doc) : Except String Unit :=
  let layout := Reference.allocateReferenceLayout s.policy inst m
  let hworkspace := Reference.reference_modMulCircuitWorkspaceOK s.policy inst m
  let hstep4 := Reference.reference_step4Workspace s.policy inst m
  let real :=
    orderFindingApprox inst.a inst.N layout.x layout.data layout.work layout.scratch
      layout.flag hworkspace hstep4
  match instantiateGate doc "shor_gate" (policyShorEnv s inst layout) 400 with
  | .error e => .error s!"policy template check (shor_gate): instantiate: {e}"
  | .ok g =>
      if gateAgrees g real then .ok ()
      else .error
        s!"policy template check (shor_gate): disagrees at N={inst.N}, m={m}"

/-- `shor` agreement at one reference instance and precision. -/
def checkPolicyShorAt (s : ShorPolicySubmission) (inst : ShorOrderFindingInstance) (m : ℕ)
    (doc : Doc) : Except String Unit :=
  let layout := Reference.allocateReferenceLayout s.policy inst m
  let real := Reference.referenceShorCircuit s.policy inst m
  match instantiate doc "shor" (policyShorEnv s inst layout) 400 with
  | .error e => .error s!"policy template check (shor): instantiate: {e}"
  | .ok g =>
      if lowGateAgrees g real then .ok ()
      else .error s!"policy template check (shor): disagrees at N={inst.N}, m={m}"

/-! ## The sampled widths -/

/-- Depth of the policy's own recursion chain from a symmetric start. -/
def policyPPRecursionDepth (P : ShorLoweringPolicy) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n =>
      let n' := policyNextWidth P n n
      if n' < n then policyPPRecursionDepth P fuel n' + 1 else 0

/-- The `qft` widths a policy is checked at: the single-table rationale (`4`,
`8`, `9` for an odd split), plus two odd widths straddling the *lowest*
threshold.

`qft` splits at `splitM r = regSize r / 2` and calls the phase product on
`(w/2, w - w/2)`, whose `max` is `⌈w/2⌉` — so `w = 2t ± 1` is where that
unequal pair straddles threshold `t`, and is the one shape neither the
phase-product ladder (always symmetric) nor a single table ever reaches.

Only the lowest threshold. What is unique to `qft` is the unequal operand
pair, and the lowest threshold exercises it; a `qft` straddling the top
threshold would unroll the whole recursion from `t₀` and test nothing the
phase-product checks do not already cover at `t₀` and `t₀ - 1`. -/
def policyQFTWidthLadder (P : ShorLoweringPolicy) : List ℕ :=
  let lowest := (P.bands.map PolicyBand.threshold).min?.getD 0
  ([4, 8, 9] ++ (if 1 ≤ lowest then [2 * lowest - 1, 2 * lowest + 1] else [])).eraseDups

/-! ## One recursive level per band

A band body instantiated at full depth unrolls every band below it, so even
the cheapest full-depth width of an upper band — its own threshold — is the
whole recursion from there down. The per-band check instead instantiates
the body one level deep: `Env.leafCall` turns each child call into the
phase-product leaf the compiler emits at that checkpoint, and the result is
compared at the `Gate` level with `compiledSignedPhaseGate` on the layout
`Policy.canonicalStep` builds. This covers the band's allocations, its
table's arithmetic, and every checkpoint's angle and register arguments,
including each child's reserve slice. A call's capacity arguments must also
equal the capacities of the registers it passes (`shallowLeafCall`), so a
document that hands a child a capacity other than the reserve it sliced is
rejected without unrolling the child. Composition across levels is covered
by the full-depth checks at `policyDepthWidths`. -/

/-- Shallow treatment of a dispatcher or leaf call: the high-level
phase-product gate on the registers the call passes, after checking the
call's capacity arguments against those registers. -/
def shallowLeafCall (controlled : Bool) :
    String → List ℕ → List Angle → List ExtReg → Option (Except String Gate)
  | name, wVals, [phi], rVals =>
      if name == dispatcherName controlled || name == dispatcherLeafName controlled then
        some (do
          let (ctrl?, x, z) ← (match controlled, rVals with
            | false, [x, z] => pure ((none : Option ExtReg), x, z)
            | true, [c, x, z] => pure (some c, x, z)
            | _, _ => throw s!"shallow call {name}: unexpected register arguments")
          match wVals with
          | [xw, zw, xCap, zCap] =>
              if xw ≠ x.width ∨ zw ≠ z.width then
                throw s!"shallow call {name}: width arguments ({xw}, {zw}) disagree with \
                  the passed registers' widths ({x.width}, {z.width})"
              if xCap ≠ x.capacity ∨ zCap ≠ z.capacity then
                throw s!"shallow call {name}: capacity arguments ({xCap}, {zCap}) disagree with \
                  the passed registers' reserves ({x.capacity}, {z.capacity})"
          | [xw, zw] =>
              if xw ≠ x.width ∨ zw ≠ z.width then
                throw s!"shallow call {name}: width arguments ({xw}, {zw}) disagree with \
                  the passed registers' widths ({x.width}, {z.width})"
          | _ => throw s!"shallow call {name}: unexpected width arguments"
          match ctrl? with
          | none => pure (Gate.SignedPhaseProd phi x z)
          | some c =>
              match c.active.qubits with
              | [qb] => pure (Gate.CSignedPhaseProd qb phi x z)
              | _ => throw s!"shallow call {name}: control register is not a single qubit")
      else none
  | _, _, _, _ => none

/-- One level of band `i`'s body against the compiler's one-level gate. -/
def policyBandBodyAgrees (s : ShorPolicySubmission) (doc : Doc) (i : ℕ) (T : ToomCookTable)
    (x z : ExtReg) (phi : Angle)
    (hT : s.policy.choose (phaseInputSize x z) = some T)
    (hws : Policy.WorkspaceOK s.policy x z) : Except String Unit :=
  let real : Gate :=
    if hrec : nextSignedWidthBy s.policy.widthRule x z T.ops < phaseInputSize x z then
      compiledSignedPhaseGateBy s.policy.widthRule T.k T.hk T.pts T.hpts T.ops phi x z
        (Policy.canonicalStep s.policy T x z hT hrec hws).layout
    else Gate.SignedPhaseProd phi x z
  let env : Env :=
    { w := fun name =>
        if name == "xw" then some x.width
        else if name == "zw" then some z.width
        else if name == "xCap" then some x.capacity
        else if name == "zCap" then some z.capacity
        else none
      a := fun name => if name == "phi" then some phi else none
      r := fun name => if name == "x" then some x else if name == "z" then some z else none
      opaqueW := policyOpaqueDispatch s.policy
      coeff := policyCoeffDispatch s
      leafCall := shallowLeafCall false }
  match instantiateGate doc (bandBodyName false i) env policyFuel with
  | .error e => .error e
  | .ok g => if gateAgrees g real then .ok () else .error "one level of the band body disagrees with the compiler's step"

/-- Controlled counterpart of `policyBandBodyAgrees`. -/
def policyCBandBodyAgrees (s : ShorPolicySubmission) (doc : Doc) (i : ℕ) (T : ToomCookTable)
    (ctrl : ℕ) (x z : ExtReg) (phi : Angle)
    (hT : s.policy.choose (phaseInputSize x z) = some T)
    (hws : Policy.CWorkspaceOK s.policy ctrl x z) : Except String Unit :=
  let real : Gate :=
    if hrec : nextSignedWidthBy s.policy.widthRule x z T.ops < phaseInputSize x z then
      compiledCSignedPhaseGateBy s.policy.widthRule T.k T.hk T.pts T.hpts T.ops ctrl phi x z
        (Policy.canonicalStep s.policy T x z hT hrec hws.toWorkspaceOK).layout
    else Gate.CSignedPhaseProd ctrl phi x z
  let ctrlReg := ExtReg.ofReg (Reg.interval ctrl 1)
  let env : Env :=
    { w := fun name =>
        if name == "xw" then some x.width
        else if name == "zw" then some z.width
        else if name == "xCap" then some x.capacity
        else if name == "zCap" then some z.capacity
        else none
      a := fun name => if name == "phi" then some phi else none
      r := fun name =>
        if name == "ctrl" then some ctrlReg
        else if name == "x" then some x else if name == "z" then some z else none
      opaqueW := policyOpaqueDispatch s.policy
      coeff := policyCoeffDispatch s
      leafCall := shallowLeafCall true }
  match instantiateGate doc (bandBodyName true i) env policyFuel with
  | .error e => .error e
  | .ok g => if gateAgrees g real then .ok () else .error "one level of the band body disagrees with the compiler's step"

/-- Band `i`'s body, one level deep, at the band's own threshold. -/
def checkPolicyBandBodyAt (s : ShorPolicySubmission) (i : ℕ) (doc : Doc) (slack : ℕ := 1) :
    Except String Unit :=
  match s.policy.bands[i]? with
  | none => .error s!"policy band check: no band {i}"
  | some b =>
    let n := b.threshold
    match policyPPRegisters s.policy n slack with
    | .error e => .error s!"policy band check (band {i}, phase_product): {e}"
    | .ok (x, z, _) =>
      match hc : chooseIdx s.policy (phaseInputSize x z) with
      | none => .error s!"policy band check: no band covers width {n}"
      | some (j, T) =>
        if j = i then
          have hT : s.policy.choose (phaseInputSize x z) = some T := by
            rw [← chooseIdx_map, hc]; rfl
          if hws : Policy.WorkspaceOK s.policy x z then
            match policyBandBodyAgrees s doc i T x z ((1 : ℚ) / 4) hT hws with
            | .ok _ => .ok ()
            | .error e =>
              .error s!"policy band check (band {i}, phase_product) at n={n}, slack={slack}: {e}"
          else .error s!"policy band check (band {i}): insufficient workspace at n={n}, slack={slack}"
        else .error s!"policy band check: width {n} is covered by band {j}, not band {i}"

/-- Controlled counterpart of `checkPolicyBandBodyAt`. -/
def checkPolicyCBandBodyAt (s : ShorPolicySubmission) (i : ℕ) (doc : Doc) (slack : ℕ := 1) :
    Except String Unit :=
  match s.policy.bands[i]? with
  | none => .error s!"policy band check: no band {i}"
  | some b =>
    let n := b.threshold
    match policyPPRegisters s.policy n slack with
    | .error e => .error s!"policy band check (band {i}, cphase_product): {e}"
    | .ok (x, z, ctrl) =>
      match hc : chooseIdx s.policy (phaseInputSize x z) with
      | none => .error s!"policy band check: no band covers width {n}"
      | some (j, T) =>
        if j = i then
          have hT : s.policy.choose (phaseInputSize x z) = some T := by
            rw [← chooseIdx_map, hc]; rfl
          if hws : Policy.CWorkspaceOK s.policy ctrl x z then
            match policyCBandBodyAgrees s doc i T ctrl x z ((1 : ℚ) / 4) hT hws with
            | .ok _ => .ok ()
            | .error e =>
              .error s!"policy band check (band {i}, cphase_product) at n={n}, slack={slack}: {e}"
          else .error s!"policy band check (band {i}): insufficient workspace at n={n}, slack={slack}"
        else .error s!"policy band check: width {n} is covered by band {j}, not band {i}"

/-! ## Full depth, within the leaf budget -/

/-- The number of schoolbook leaves a phase product at width `n` unrolls
to under the policy: `2k - 1` per recursing node, `1` at a leaf. The gate
count of the full-depth circuit is roughly proportional to it. -/
def policyLeafCount (P : ShorLoweringPolicy) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | fuel + 1, n =>
      match P.choose n with
      | none => 1
      | some T =>
          let n' := policyNextWidth P n n
          if n' < n then q T.k * policyLeafCount P fuel n' else 1

/-- The largest leaf count a full-depth instantiation may have. Widths
above it are covered one level deep by the per-band check instead. -/
def policyFullDepthLeafBudget : ℕ := 100

/-! ## The probe submission

A best-known policy's thresholds are `Θ(n)`, and the evaluation works on
concrete qubit lists, so sampling at the submission's own thresholds costs
time that grows with `n`. Nothing the sampled checks test depends on the
thresholds except the dispatcher:

* each band body is extracted from `Policy.stepPlan` at band `i`, and names
  only its table, its position (the `coeff` offset) and the opaque oracles —
  never a threshold;
* the dispatcher is *built*, not extracted (`dispatcherTemplate`), and its
  routing is a theorem (`IR.dispatcherCallAt_dispatcherTemplate`).

So the tier is run on the **probe submission**: the same setups in the same
band order, at the smallest strictly decreasing thresholds at which each
band's table shrinks (or, for a table that shrinks nowhere in the search
window, the smallest width above the previous band: the compiler takes the
leaf there, and the body check verifies the leaf branch of the band's guard),
together with the document whose two dispatchers are rebuilt for those
thresholds. Every check keeps its meaning — band bodies
one level deep, full depth within the leaf budget, `qft`, leaves, Shor
instances — at widths that depend only on the tables. What ties the result
to the submitted document is checked separately: its dispatchers must be
exactly `dispatcherTemplate s.policy`, and the probe document differs from
it in those two templates only. -/

/-- Width of the search window for a probe threshold, starting at the width
above the previous band: above every table's smallest shrinking width in the
shipped catalogs (`k ≤ 16`: about `1130`), with room for a 64-band probe
ladder. -/
def probeSearchBound : ℕ := 4096

/-- The smallest width `≥ lo` at which `T`'s step shrinks a symmetric
operand pair (the condition `bandShrinks` evaluates, at one width). -/
def probeShrinkWidth (T : ToomCookTable) (lo : ℕ) : Option ℕ :=
  (List.range' lo probeSearchBound).find? fun w =>
    decide (RecursivePhaseWorkspace.nextWidth T.ops w w < w)

/-- Probe thresholds for setups listed **narrowest band first**: each the
smallest shrinking width strictly above the previous one. A table that
shrinks nowhere in the window is probed at `lo` itself: such a band is dead
weight, never unsound (`ShorLoweringPolicy.Stops` sends it to the leaf), and
at a non-shrinking width `policyBandBodyAgrees` compares the band body
against the leaf, which is exactly what the compiler emits there. -/
def probeThresholdsRev : List ShorLoweringSetup → ℕ → Option (List ℕ)
  | [], _ => some []
  | b :: bs, lo => do
      let t := (probeShrinkWidth b.table lo).getD lo
      let rest ← probeThresholdsRev bs (t + 1)
      pure (t :: rest)

/-- The probe submission: `s`'s setups, same order, probe thresholds. -/
def probeSubmission (s : ShorPolicySubmission) : Option ShorPolicySubmission :=
  match probeThresholdsRev (s.bands.reverse.map Prod.snd) 2 with
  | none => none
  | some tsRev =>
      let bands := (tsRev.reverse).zip (s.bands.map Prod.snd)
      if bands.length ≠ s.bands.length then none
      else if h : (bands.map Prod.fst).IsChain (· > ·) then
        some { bands := bands, sorted := h, widthRule := s.widthRule }
      else none

/-- `doc` with both dispatchers rebuilt for policy `P`. -/
def withDispatchers (doc : Doc) (P : ShorLoweringPolicy) : Doc :=
  { doc with templates := doc.templates.map fun t =>
      if t.name == dispatcherName false then dispatcherTemplate P false
      else if t.name == dispatcherName true then dispatcherTemplate P true
      else t }

/-- `doc`'s dispatchers are exactly the ones built for `P` (and both exist). -/
def dispatchersAre (doc : Doc) (P : ShorLoweringPolicy) : Bool :=
  (doc.templates.find? (·.name == dispatcherName false)) == some (dispatcherTemplate P false)
    && (doc.templates.find? (·.name == dispatcherName true)) == some (dispatcherTemplate P true)

/-! ## Distinct tables are checked once

Best-known policies at large `n` repeat a few tables over many bands. The extractor reuses the body of
the first band with a given table for every later band with the same table, with its `coeff` indices
shifted by the offset difference (`Driver.policyBandBodies`, `IR.shiftCoeffN`). The tier therefore runs
its sampled band-body checks once per distinct table, and for every later band checks *symbolically*
that its bodies are exactly that shifted copy. Under the `coeff` oracle the shifted indices resolve to
the later band's own points, which are equal to the earlier band's (`sameSetup`). -/

/-- An injective key per operation, so programs over different `k` compare without `DecidableEq`. -/
def opKey {k : ℕ} : Operations.valid_ops k → ℕ × ℕ × ℕ × Bool × ℕ
  | .shiftL i n => (0, i.val, 0, false, n)
  | .shiftR i n => (1, i.val, 0, false, n)
  | .negate i => (2, i.val, 0, false, 0)
  | .addScaled d s ng sh => (3, d.val, s.val, ng, sh)
  | .phaseProduct i => (4, i.val, 0, false, 0)

/-- Same table: same `k`, same interpolation points, same program. -/
def sameSetup (a b : ShorLoweringSetup) : Bool :=
  a.k == b.k && decide (a.pts = b.pts) && a.ops.map opKey == b.ops.map opKey

/-- `Registry.coeffOffset` of every band, in band order. -/
def bandOffsets (s : ShorPolicySubmission) : List ℕ :=
  (s.bands.foldl (fun (acc, off) b => (acc ++ [off], off + q b.2.k)) ([], 0)).1

/-- The first earlier band with the same table as band `i`, if any. -/
def firstSameBand (s : ShorPolicySubmission) (i : ℕ) : Option ℕ :=
  match s.bands[i]? with
  | none => none
  | some bi => (List.range i).find? fun j =>
      match s.bands[j]? with
      | some bj => sameSetup bj.2 bi.2
      | none => false

/-- Band `i`'s body of one flavour is exactly band `j`'s, renamed, with `coeff` indices shifted by `d`. -/
def bandCopyOK (doc : Doc) (controlled : Bool) (i j d : ℕ) : Bool :=
  match doc.templates.find? (·.name == bandBodyName controlled i),
        doc.templates.find? (·.name == bandBodyName controlled j) with
  | some ti, some tj =>
      ti.body == shiftCoeffN d tj.body && ti.wParams == tj.wParams && ti.aParams == tj.aParams
        && ti.rParams == tj.rParams
  | _, _ => false

/-- The widths reaching one, two and three levels of the policy's own recursion, within the leaf budget
(the band boundaries need no sampling: their routing is the proved dispatcher). -/
def policyDepthWidths (P : ShorLoweringPolicy) : List ℕ :=
  ([1, 2, 3].filterMap fun d =>
    (List.range widthSearchBound).find? fun n => d ≤ policyPPRecursionDepth P widthSearchBound n).eraseDups
    |>.filter fun n => policyLeafCount P widthSearchBound n ≤ policyFullDepthLeafBudget

/-- The evaluation tier on a probe submission `s'` and document `doc'`: band bodies one level deep for
the first band of each distinct table, shifted-copy identity for the others, full depth at the
recursion-depth ladder within the leaf budget, then `qft`, the leaves and the Shor instances as for
a single table (`submissionChecks` in `Verify.lean`). -/
def policyProbeChecks (s' : ShorPolicySubmission) (doc' : Doc) : Bool :=
  let offs := bandOffsets s'
  let bands := List.range s'.bands.length
  let ppW := policyDepthWidths s'.policy
  let qftW := policyQFTWidthLadder s'.policy
  bands.all (fun i =>
      match firstSameBand s' i with
      | some j =>
          let d := offs.getD i 0 - offs.getD j 0
          bandCopyOK doc' false i j d && bandCopyOK doc' true i j d
      | none =>
          submissionPPSlacks.all (fun sl => okB (checkPolicyBandBodyAt s' i doc' sl))
            && submissionPPSlacks.all (fun sl => okB (checkPolicyCBandBodyAt s' i doc' sl)))
    && ppW.all (fun n => submissionPPSlacks.all fun sl => okB (checkPolicyPhaseProductAt s' n doc' sl))
    && ppW.all (fun n => submissionPPSlacks.all fun sl => okB (checkPolicyCPhaseProductAt s' n doc' sl))
    && qftW.all (fun w => okB (checkPolicyQftAt s' w doc'))
    && submissionLeafWidths.all (fun p => okB (checkNaiveLeafAt doc' p.1 p.2))
    && submissionLeafWidths.all (fun p => okB (checkNaiveCLeafAt doc' p.1 p.2))
    && submissionShorGateInstances.all (fun im => okB (checkPolicyShorGateAt s' im.1 im.2 doc'))
    && submissionShorInstances.all (fun im => okB (checkPolicyShorAt s' im.1 im.2 doc'))

/-- **The policy evaluation tier**, as one `Bool`, evaluated natively by the
`forshor_policy_submission` executable (`Submission/PolicyMain.lean`).

The submitted document is well formed and carries exactly the dispatchers built for its own policy
(whose routing is a theorem); the sampled checks are `policyProbeChecks` on the probe submission and
the probe document. The cost depends on the distinct tables only: not on the thresholds, so not on `n`,
and not on how many bands repeat a table. -/
def policySubmissionChecks (s : ShorPolicySubmission) (doc : Doc) : Bool :=
  doc.wellFormed && dispatchersAre doc s.policy &&
    match probeSubmission s with
    | none => false
    | some s' => policyProbeChecks s' (withDispatchers doc s'.policy)

/-! ### Probes at exact-width thresholds (`--probe-exact`)

`probeShrinkWidth` places the probes where the scan first shrinks each table,
whatever the policy's width rule: the instance sizes the tier has always
checked. Under the exact rule a table shrinks at much smaller widths (shipped
`k = 2` table: from 5 rather than 14), and since the exact width never exceeds
the scan (`nextSignedWidthBy_exact_le_scan`), every band still recurses at its
scan probe threshold. The variant below probes where the policy's own rule
first shrinks each table instead: the same checks, run deeper and on much
larger circuits. -/

/-- `probeShrinkWidth` under the policy's width rule. -/
def probeShrinkWidthBy (R : WidthRule) (T : ToomCookTable) (lo : ℕ) : Option ℕ :=
  (List.range' lo probeSearchBound).find? fun w =>
    decide (RecursivePhaseWorkspace.nextWidthBy R T.ops w w < w)

/-- `probeThresholdsRev` under a width rule. -/
def probeThresholdsRevBy (R : WidthRule) : List ShorLoweringSetup → ℕ → Option (List ℕ)
  | [], _ => some []
  | b :: bs, lo => do
      let t := (probeShrinkWidthBy R b.table lo).getD lo
      let rest ← probeThresholdsRevBy R bs (t + 1)
      pure (t :: rest)

/-- `probeSubmission` with the thresholds of the submission's own width rule. -/
def probeSubmissionOwnRule (s : ShorPolicySubmission) : Option ShorPolicySubmission :=
  match probeThresholdsRevBy s.widthRule (s.bands.reverse.map Prod.snd) 2 with
  | none => none
  | some tsRev =>
      let bands := (tsRev.reverse).zip (s.bands.map Prod.snd)
      if bands.length ≠ s.bands.length then none
      else if h : (bands.map Prod.fst).IsChain (· > ·) then
        some { bands := bands, sorted := h, widthRule := s.widthRule }
      else none

/-- `policySubmissionChecks` with probes where the submission's own width
rule shrinks each table (`forshor_policy_submission --probe-exact`). -/
def policySubmissionChecksOwnRuleProbe (s : ShorPolicySubmission) (doc : Doc) : Bool :=
  doc.wellFormed && dispatchersAre doc s.policy &&
    match probeSubmissionOwnRule s with
    | none => false
    | some s' => policyProbeChecks s' (withDispatchers doc s'.policy)

end Shor.Reflect
