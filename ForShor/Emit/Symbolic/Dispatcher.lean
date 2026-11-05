import ForShor.Emit.IR.Syntax
import ForShor.ShorVerification.Framework.Policy

/-!
# The width dispatcher, as a template

Every other template in a `Doc` is *extracted*: a Lean term is read by
reflection and translated construct by construct. This one is not, because
there is no term to read. A policy's choice of table at a width is
`ShorLoweringPolicy.choose`, which is a `List.find?` over the bands — data,
not a circuit — and the dispatcher is that `find?` spelled as a chain of
`Node.cond` guards.

So this file is a plain function from a policy to an `IR.Template`, with no
`MetaM`, no `Expr` and no trust in the translation table. What it *does* need
is to agree with `choose`, and `dispatcherCallAt_dispatcherTemplate` below proves it
rather than sampling it: if the emitted guards and `choose` ever disagreed,
the extracted document would route a width to a band whose body was built for
a different table, and every tier downstream would still pass.

## Shape

For bands `[(t₀, T₀), (t₁, T₁), …]`, widest first:

```
cond (t₀ ≤ max xw zw) → call "phase_product_0"
cond (t₁ ≤ max xw zw) → call "phase_product_1"
…
                      → call "naive_leaf"
```

Three things this has to get right, each a direct reading of
`Framework/Policy.lean`:

* **Guard on `max xw zw`**, because `choose` is keyed on
  `phaseInputSize x z = max x.width z.width`.
* **Band order, `≤`, first match wins.** `choose` is
  `bands.find? (fun b => decide (b.threshold ≤ n))`, so the chain must be
  right-nested in list order, not a set of disjoint range tests.
  `ShorPolicySubmission.sorted` is what makes those two descriptions agree;
  nothing here needs it, which is why nothing here assumes it.
* **The fallthrough is the naive leaf**, matching `choose = none`'s
  `PhaseLoweringPlan.signedBase`.

The parameter lists are exactly the ones `extractPhaseProductBody` gives the
single-table `phase_product`, so `qft`'s call into the phase product, `shor`'s,
and the band bodies' own self-calls all type-check against the dispatcher with
no edit: `Extract.lean`'s `Policy.signedPlan`/`signedPlanOf` cases already
emit `call "phase_product"`, and that name is now this template.
-/

namespace Shor
namespace IR

/-- `phase_product` / `cphase_product`: the dispatcher's own name, and the
prefix its per-band bodies are named with. -/
def dispatcherName (controlled : Bool) : String :=
  if controlled then "cphase_product" else "phase_product"

/-- `naive_leaf` / `naive_cleaf`: what a width below the last threshold
falls through to. -/
def dispatcherLeafName (controlled : Bool) : String :=
  if controlled then "naive_cleaf" else "naive_leaf"

/-- Band `i`'s body template name. -/
def bandBodyName (controlled : Bool) (i : ℕ) : String :=
  s!"{dispatcherName controlled}_{i}"

/-- The register arguments every call in the chain passes on unchanged.
`ctrl` leads for the controlled chain, matching `naive_cleaf`'s `rParams` and
`Extract.lean`'s `cSignedPlan` call site. -/
def dispatcherRArgs (controlled : Bool) : List RegExpr :=
  if controlled then [.var "ctrl", .var "x", .var "z"] else [.var "x", .var "z"]

/-- The guard chain, structurally recursive on the bands with the band index
carried explicitly.

Written this way rather than as a `foldr` over `zipIdx` so that the agreement
proof below is an ordinary list induction with `i` generalised. -/
def dispatcherChain (controlled : Bool) : ℕ → List PolicyBand → Node
  | _, [] =>
      .call (dispatcherLeafName controlled) [.var "xw", .var "zw"]
        [.var "phi"] (dispatcherRArgs controlled)
  | i, b :: bs =>
      .cond (.le (.lit b.threshold) (.max (.var "xw") (.var "zw")))
        (.call (bandBodyName controlled i)
          [.var "xw", .var "zw", .var "xCap", .var "zCap"]
          [.var "phi"] (dispatcherRArgs controlled))
        (dispatcherChain controlled (i + 1) bs)

/-- The dispatcher for `P`: one template, named `phase_product`, whose body
routes a width to the band `P.choose` picks. -/
def dispatcherTemplate (P : ShorLoweringPolicy) (controlled : Bool) : Template :=
  { name := dispatcherName controlled
    wParams := ["xw", "zw", "xCap", "zCap"]
    aParams := ["phi"]
    rParams := if controlled then ["ctrl", "x", "z"] else ["x", "z"]
    body := dispatcherChain controlled 0 P.bands
    provenance := "Shor.ShorLoweringPolicy.choose (built, not extracted)" }

/-! ## That it agrees with `choose`

`dispatcherCallAt` walks an emitted chain at concrete widths and reports the
template it lands on. It handles only the node shapes `dispatcherChain`
produces — it is an oracle for *this* function, not a general evaluator, and
`IR/Instantiate.lean` remains the real one.

The agreement is stated against `chooseIdx`, which is `choose` with the band's
*index* attached, because the index is what the chain names. `chooseIdx_map`
then says `chooseIdx` and `choose` pick the same table, so the two theorems
together say: the dispatcher calls band `j`'s body exactly where the policy
picks band `j`'s table, and the leaf exactly where it picks nothing. -/

/-- The template a dispatcher chain calls at concrete widths. -/
def dispatcherCallAt : Node → ℕ → ℕ → Option String
  | .call t _ _ _, _, _ => some t
  | .cond (.le (.lit t) (.max (.var "xw") (.var "zw"))) ifTrue ifFalse, xw, zw =>
      if t ≤ max xw zw then dispatcherCallAt ifTrue xw zw
      else dispatcherCallAt ifFalse xw zw
  | _, _, _ => none

/-- `ShorLoweringPolicy.choose`'s scan with the band index carried along:
the first band whose threshold is `≤ n`, paired with its position. This is
the recursion `dispatcherChain` mirrors node for node. -/
def chooseIdxFrom (n : ℕ) : ℕ → List PolicyBand → Option (ℕ × ToomCookTable)
  | _, [] => none
  | i, b :: bs => if b.threshold ≤ n then some (i, b.table) else chooseIdxFrom n (i + 1) bs

/-- `choose` at `n`, with the chosen band's index. -/
def chooseIdx (P : ShorLoweringPolicy) (n : ℕ) : Option (ℕ × ToomCookTable) :=
  chooseIdxFrom n 0 P.bands

/-- `chooseIdx` picks the table `choose` picks. The index is extra
information, not a different answer. -/
theorem chooseIdx_map (P : ShorLoweringPolicy) (n : ℕ) :
    (chooseIdx P n).map Prod.snd = P.choose n := by
  show (chooseIdxFrom n 0 P.bands).map Prod.snd = _
  rw [ShorLoweringPolicy.choose]
  suffices h : ∀ (i : ℕ) (bs : List PolicyBand),
      (chooseIdxFrom n i bs).map Prod.snd
        = (bs.find? (fun b => decide (b.threshold ≤ n))).map PolicyBand.table from h 0 P.bands
  intro i bs
  induction bs generalizing i with
  | nil => rfl
  | cons b bs ih =>
      rw [chooseIdxFrom, List.find?_cons]
      by_cases hb : b.threshold ≤ n
      · simp [hb]
      · simp [hb, ih (i + 1)]

/-- The chain routes by `≤` on `max xw zw`, in band order, naming the band it
lands on and falling through to the leaf. -/
theorem dispatcherCallAt_chain (controlled : Bool) (xw zw : ℕ) :
    ∀ (i : ℕ) (bs : List PolicyBand),
      dispatcherCallAt (dispatcherChain controlled i bs) xw zw
        = some (match chooseIdxFrom (max xw zw) i bs with
                | some (j, _) => bandBodyName controlled j
                | none => dispatcherLeafName controlled)
  | _, [] => rfl
  | i, b :: bs => by
      show dispatcherCallAt
          (.cond (.le (.lit b.threshold) (.max (.var "xw") (.var "zw"))) _ _) xw zw = _
      rw [dispatcherCallAt, chooseIdxFrom]
      by_cases hb : b.threshold ≤ max xw zw
      · simp [hb, dispatcherCallAt]
      · simp [hb, dispatcherCallAt_chain controlled xw zw (i + 1) bs]

/-- **The dispatcher agrees with the policy.** It calls band `j`'s body
exactly where `chooseIdx` picks band `j`, and `naive_leaf` exactly where the
policy offers no table.

With `chooseIdx_map`, this is the statement that the emitted guards and
`ShorLoweringPolicy.choose` cannot drift apart: a width routed to
`phase_product_j` is a width at which the policy really does choose band
`j`'s table, and `phase_product_j` is the body for that table — extracted
from it, or (when an earlier band has the same table) that band's body
renamed with its `coeff` indices shifted (`Driver.policyBandBodies`). -/
theorem dispatcherCallAt_dispatcherTemplate (P : ShorLoweringPolicy) (controlled : Bool)
    (xw zw : ℕ) :
    dispatcherCallAt (dispatcherTemplate P controlled).body xw zw
      = some (match chooseIdx P (max xw zw) with
              | some (j, _) => bandBodyName controlled j
              | none => dispatcherLeafName controlled) :=
  dispatcherCallAt_chain controlled xw zw 0 P.bands

end IR
namespace IR

/-! ## Shifting `coeff` indices

Used by the extractor to reuse a band body for a repeated table (`Driver.policyBandBodies`) and by the evaluation tier to check that a reused body is exactly that copy (`PolicyVerify.bandCopyOK`). -/

/-- Shift every `coeff` point index in an angle expression by `d`. -/
partial def shiftCoeffA (d : ℕ) : AExpr → AExpr
  | .coeff phi l m => .coeff (shiftCoeffA d phi) (l + d) m
  | .mul a w => .mul (shiftCoeffA d a) w
  | .div2 a => .div2 (shiftCoeffA d a)
  | .neg a => .neg (shiftCoeffA d a)
  | .signedPair phi xi xw zi zw => .signedPair (shiftCoeffA d phi) xi xw zi zw
  | a => a

/-- Shift every `coeff` point index in a template body by `d`. -/
partial def shiftCoeffN (d : ℕ) : Node → Node
  | .op name regs nats angle flags => .op name regs nats (angle.map (shiftCoeffA d)) flags
  | .seq body => .seq (body.map (shiftCoeffN d))
  | .adj body => .adj (shiftCoeffN d body)
  | .cond g t e => .cond g (shiftCoeffN d t) (shiftCoeffN d e)
  | .call t wArgs aArgs rArgs => .call t wArgs (aArgs.map (shiftCoeffA d)) rArgs
  | .loop v lo hi body => .loop v lo hi (shiftCoeffN d body)

end IR

end Shor
