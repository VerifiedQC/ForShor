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
in one. So a single width check covers every layer, and a width at the top
of the policy covers every band the chain descends through. That is why the
ladder below is built from the policy's own `nextWidth` chain *and* from its
band boundaries: the first finds widths where the recursion is deep, the
second finds widths where it changes table.

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
  | some T => RecursivePhaseWorkspace.nextWidth T.ops wx wz
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

/-- Every band boundary, as a width just inside the band and one just below
it. These are the widths at which the dispatcher's answer changes, so they
are where a guard that is off by one would show. -/
def policyBoundaryWidths (P : ShorLoweringPolicy) : List ℕ :=
  P.bands.flatMap fun b =>
    (if 0 < b.threshold then [b.threshold - 1] else []) ++ [b.threshold]

/-- The phase-product widths a policy is checked at: its band boundaries,
plus the smallest widths reaching one, two and three levels of its own
recursion.

The boundaries are what a single table never needed — they are where the
chain changes table — and the depth ladder is `ppWidthLadder`'s rationale
carried over unchanged: three levels is what makes a *grandchild* of a
recursive call exist. -/
def policyPPWidthLadder (P : ShorLoweringPolicy) : List ℕ :=
  let depths := [1, 2, 3].filterMap fun d =>
    (List.range widthSearchBound).find? fun n => d ≤ policyPPRecursionDepth P widthSearchBound n
  (policyBoundaryWidths P ++ depths).eraseDups

/-- The `qft` widths a policy is checked at: the single-table rationale (`4`,
`8`, `9` for an odd split), plus two odd widths straddling the *lowest*
threshold.

`qft` splits at `splitM r = regSize r / 2` and calls the phase product on
`(w/2, w - w/2)`, whose `max` is `⌈w/2⌉` — so `w = 2t ± 1` is where that
unequal pair straddles threshold `t`, and is the one shape neither the
phase-product ladder (always symmetric) nor a single table ever reaches.

Only the lowest threshold, deliberately. Straddling the *top* threshold
would mean a `qft` at `w ≈ 2·t₀`, whose embedded phase product starts at
`t₀` and recurses all the way down — the most expensive check in the suite,
and one that tests nothing the phase-product ladder does not already test at
`t₀` and `t₀ - 1` directly. What is unique here is the unequal pair, and the
lowest threshold exercises it at a width that costs seconds rather than
minutes. -/
def policyQFTWidthLadder (P : ShorLoweringPolicy) : List ℕ :=
  let lowest := (P.bands.map PolicyBand.threshold).min?.getD 0
  ([4, 8, 9] ++ (if 1 ≤ lowest then [2 * lowest - 1, 2 * lowest + 1] else [])).eraseDups

/-- **The policy evaluation tier**, as one `Bool` a submission can pin.

Mirrors `submissionChecks` check for check. The leaf templates are
table-independent, so their existing checks are reused verbatim. -/
def policySubmissionChecks (s : ShorPolicySubmission) (doc : Doc) : Bool :=
  let ppW := policyPPWidthLadder s.policy
  let qftW := policyQFTWidthLadder s.policy
  doc.wellFormed
    && ppW.all (fun n => submissionPPSlacks.all fun sl => okB (checkPolicyPhaseProductAt s n doc sl))
    && ppW.all (fun n => submissionPPSlacks.all fun sl => okB (checkPolicyCPhaseProductAt s n doc sl))
    && qftW.all (fun w => okB (checkPolicyQftAt s w doc))
    && submissionLeafWidths.all (fun p => okB (checkNaiveLeafAt doc p.1 p.2))
    && submissionLeafWidths.all (fun p => okB (checkNaiveCLeafAt doc p.1 p.2))
    && submissionShorGateInstances.all (fun im => okB (checkPolicyShorGateAt s im.1 im.2 doc))
    && submissionShorInstances.all (fun im => okB (checkPolicyShorAt s im.1 im.2 doc))

end Shor.Reflect
