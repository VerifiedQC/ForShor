import ForShor.ShorVerification.Implementation.Shor.Statement

/-!
# Balanced phase products: the two passes and the claims

ForShor's phase product cuts both operands at one common limb width, so at a
site with operands of unequal width (Step 4 at `n = 2048` is `2348 × 4399`) the
wider operand's top chunk takes the whole remainder, and the recursion is
expensive. Balancing rewrites such a site before lowering: the wider operand is
cut into blocks, and each block is multiplied by the whole narrower operand at a
common width, with ordinary equal-width phase products. The phases add up:
`φ·x·z = Σ_b (φ·2^{offset_b})·x_b·z`. The equal-width core is untouched.

There are two versions of the pass, built from the same split:

* **`balance`, the conditional pass.** A site is split only if the decidable
  check `fitsB` says the operands' existing spare qubits hold every block;
  otherwise the site is left as it is. So this pass needs nothing of the layout:
  it is correct under the source circuit's own preconditions, on any layout.
  The price is that the circuit's shape depends on the spare qubits.

* **`balanceU`, the unconditional pass.** Every site the rule has a plan for is
  split, with no check. It is correct wherever every site's plan fits (`Fits`),
  and `balanceU` is then `balance`. The reference layout is sized so that this
  always holds for the default rule, which is why `balancedUShorImplementation`
  takes no hypothesis and why its qubit count depends on the register widths
  alone.

Widths enter only through the plan rule `Rule` (block widths and targets, from
the two operand widths) and the core's reserve function `Policy.reserveNeed P`.
The claims at the end are what `Main.lean` proves: each pass keeps the workspace
and the semantics, and Shor's circuit lowered after each pass keeps its success
bound. The reference circuits and the packaged implementations are built in
`Main.lean`.
-/

namespace Shor
namespace Balanced

open Gate

/-! ## Blocks of a register -/

theorem disjoint_take_of (r s : Reg) (n : ℕ) (h : Disjoint r s) : Disjoint (r.take n) s := by
  unfold Disjoint at *
  exact List.disjoint_of_subset_left (List.take_subset n r.qubits) h

theorem disjoint_drop_of (r s : Reg) (n : ℕ) (h : Disjoint r s) : Disjoint (r.drop n) s := by
  unfold Disjoint at *
  exact List.disjoint_of_subset_left (List.drop_subset n r.qubits) h

/-- The low `w` active qubits of `x`, owning the whole reserve of `x`. -/
def lowBlock (x : ExtReg) (w : ℕ) : ExtReg :=
  ⟨x.active.take w, x.reserve, disjoint_take_of _ _ w x.active_reserve_disjoint⟩

/-- The active qubits of `x` above the first `w`, owning the whole reserve of `x`. -/
def highPart (x : ExtReg) (w : ℕ) : ExtReg :=
  ⟨x.active.drop w, x.reserve, disjoint_drop_of _ _ w x.active_reserve_disjoint⟩

/-- Which phase-product gate a block uses: the site's own kind. -/
inductive Ctl
  | none
  | ctrl (q : ℕ)
  deriving DecidableEq

/-- The phase-product gate of kind `c`. -/
def Ctl.gate : Ctl → Angle → ExtReg → ExtReg → Gate
  | .none, φ, x, z => Gate.SignedPhaseProd φ x z
  | .ctrl q, φ, x, z => Gate.CSignedPhaseProd q φ x z

/-! ## Plans and rules -/

/-- One lower block: `w` bits of the split operand, product run at common width `t`. -/
structure Block where
  w : ℕ
  t : ℕ
  deriving DecidableEq, Repr

/-- A balancing plan for a split operand: lower blocks (least significant first)
and the common width of the top block's product. `lower = []` is padding. -/
structure Plan where
  lower : List Block
  top : ℕ
  deriving DecidableEq, Repr

/-- A width rule: given (big width, small width), an optional plan for the big operand. -/
structure Rule where
  plan : ℕ → ℕ → Option Plan

/-- The default rule. With `s` the small width and `L > s` the big one:

* `2L ≤ 3s`: pad the small operand to `L` (no lower block);
* otherwise `B = ⌈L / s⌉` blocks: `B - 1` lower blocks of width `s - 1` (one zero
  bit makes them `s` wide) and the top block, every product at the common width
  `max s top`.

At `n = 2048` this is the searched optimum under both width rules. -/
def defaultPlan (L s : ℕ) : Option Plan :=
  if s < 2 ∨ L ≤ s then none
  else if 2 * L ≤ 3 * s then some ⟨[], L⟩
  else
    let B := (L + s - 1) / s
    let w := s - 1
    let top := L - (B - 1) * w
    let t := max s top
    some ⟨List.replicate (B - 1) ⟨w, t⟩, t⟩

def defaultRule : Rule := ⟨defaultPlan⟩

/-! ## The spare qubits a split needs -/

/-! ## The split -/

/-- One lower block: zero-extend the block to `t` (at least one bit, so it reads
unsigned), sign-extend the small operand to `t`, multiply, undo the extensions. -/
def lowGate (c : Ctl) (φ : Angle) (x z : ExtReg) (w t : ℕ) : Gate :=
  Gate.zeroExtend (lowBlock x w) (t - w) ;;
  Gate.signExtend z (t - z.width) ;;
  c.gate φ ((lowBlock x w).grow (t - w)) (z.grow (t - z.width)) ;;
  Gate.signDealloc z (t - z.width) ;;
  Gate.zeroDealloc (lowBlock x w) (t - w)

/-- The signed top block: sign-extend both to `t`, multiply, undo. -/
def topGate (c : Ctl) (φ : Angle) (x z : ExtReg) (t : ℕ) : Gate :=
  Gate.signExtend x (t - x.width) ;;
  Gate.signExtend z (t - z.width) ;;
  c.gate φ (x.grow (t - x.width)) (z.grow (t - z.width)) ;;
  Gate.signDealloc z (t - z.width) ;;
  Gate.signDealloc x (t - x.width)

/-- The balanced split of `x` against `z`: the low block at angle `φ`, the rest of
`x` recursively at angle `φ · 2^w`. -/
def splitGate (c : Ctl) : Angle → List Block → ℕ → ExtReg → ExtReg → Gate
  | φ, [], t, x, z => topGate c φ x z t
  | φ, b :: bs, t, x, z =>
      lowGate c φ x z b.w b.t ;; splitGate c (φ * 2 ^ b.w) bs t (highPart x b.w) z

/-! ## The spare qubits a split needs -/

/-- The reserve every block of a plan needs: on the split operand its extension
bits plus `Policy.reserveNeed` at the block's width, on the small operand its
extension bits plus the other half; each the largest over the blocks. -/
def planNeed (P : ShorLoweringPolicy) : List Block → ℕ → ℕ → ℕ → ℕ × ℕ
  | [], t, xw, zw =>
      ((t - xw) + (Policy.reserveNeed P t t).1, (t - zw) + (Policy.reserveNeed P t t).2)
  | b :: bs, t, xw, zw =>
      (max ((b.t - b.w) + (Policy.reserveNeed P b.t b.t).1) (planNeed P bs t (xw - b.w) zw).1,
       max ((b.t - zw) + (Policy.reserveNeed P b.t b.t).2) (planNeed P bs t (xw - b.w) zw).2)

/-- The reserve the rule's plan needs at a site, on its `x` and its `z`. -/
def siteNeed (P : ShorLoweringPolicy) (R : Rule) (wx wz : ℕ) : ℕ × ℕ :=
  if wz < wx then
    match R.plan wx wz with
    | some p => planNeed P p.lower p.top wx wz
    | none => (0, 0)
  else if wx < wz then
    match R.plan wz wx with
    | some p => ((planNeed P p.lower p.top wz wx).2, (planNeed P p.lower p.top wz wx).1)
    | none => (0, 0)
  else (0, 0)

/-! ## The conditional pass: `balance`

A site is split only where `fitsB` holds: every block is well formed, and the
operands' existing spare qubits hold every block's extension bits plus the
reserve its product needs. Otherwise the site is left as it is. -/

/-- The fit check. -/
def fitsB (P : ShorLoweringPolicy) : List Block → ℕ → ExtReg → ExtReg → Bool
  | [], t, x, z =>
      decide (x.width ≤ t) && decide (z.width ≤ t) &&
      decide ((t - x.width) + (Policy.reserveNeed P t t).1 ≤ x.capacity) &&
      decide ((t - z.width) + (Policy.reserveNeed P t t).2 ≤ z.capacity)
  | b :: bs, t, x, z =>
      decide (b.w < x.width) && decide (b.w + 1 ≤ b.t) && decide (z.width ≤ b.t) &&
      decide ((b.t - b.w) + (Policy.reserveNeed P b.t b.t).1 ≤ x.capacity) &&
      decide ((b.t - z.width) + (Policy.reserveNeed P b.t b.t).2 ≤ z.capacity) &&
      fitsB P bs t (highPart x b.w) z

/-- Balance one site of kind `c`: split the wider operand with the rule's plan when
it fits the existing spare qubits; otherwise keep the site. -/
def siteGate (P : ShorLoweringPolicy) (R : Rule) (c : Ctl) (φ : Angle) (x z : ExtReg) : Gate :=
  if z.width < x.width then
    match R.plan x.width z.width with
    | some p => if fitsB P p.lower p.top x z then splitGate c φ p.lower p.top x z else c.gate φ x z
    | none => c.gate φ x z
  else if x.width < z.width then
    match R.plan z.width x.width with
    | some p => if fitsB P p.lower p.top z x then splitGate c φ p.lower p.top z x else c.gate φ x z
    | none => c.gate φ x z
  else c.gate φ x z

/-- The conditional pass: every signed and controlled signed phase product becomes
its `siteGate`. QFTs are left alone: their twiddle sites differ by at most one bit
and are lowered inside `Policy.lowerQFT`. -/
def balance (P : ShorLoweringPolicy) (R : Rule) : Gate → Gate
  | .seq U V => .seq (balance P R U) (balance P R V)
  | .adj U => .adj (balance P R U)
  | .SignedPhaseProd φ x z => siteGate P R .none φ x z
  | .CSignedPhaseProd q φ x z => siteGate P R (.ctrl q) φ x z
  | G => G

/-! ## The unconditional pass: `balanceU`

Every site the rule has a plan for is split, with no check. `Fits` is the
condition under which that is sound: the rule's plan fits at every site of the
circuit, which is exactly what `fitsB` would have checked. -/

/-- Balance a site whenever the rule has a plan for it. -/
def siteGateU (R : Rule) (c : Ctl) (φ : Angle) (x z : ExtReg) : Gate :=
  if z.width < x.width then
    match R.plan x.width z.width with
    | some p => splitGate c φ p.lower p.top x z
    | none => c.gate φ x z
  else if x.width < z.width then
    match R.plan z.width x.width with
    | some p => splitGate c φ p.lower p.top z x
    | none => c.gate φ x z
  else c.gate φ x z

/-- The unconditional pass: every signed and controlled signed phase product
becomes its `siteGateU`. -/
def balanceU (R : Rule) : Gate → Gate
  | .seq U V => .seq (balanceU R U) (balanceU R V)
  | .adj U => .adj (balanceU R U)
  | .SignedPhaseProd φ x z => siteGateU R .none φ x z
  | .CSignedPhaseProd q φ x z => siteGateU R (.ctrl q) φ x z
  | G => G

/-- The rule's plan at a site fits the operands' spare qubits. -/
def SiteFits (P : ShorLoweringPolicy) (R : Rule) (x z : ExtReg) : Prop :=
  if z.width < x.width then
    ∀ p, R.plan x.width z.width = some p → fitsB P p.lower p.top x z = true
  else if x.width < z.width then
    ∀ p, R.plan z.width x.width = some p → fitsB P p.lower p.top z x = true
  else True

/-- Every phase-product site's plan fits. -/
def Fits (P : ShorLoweringPolicy) (R : Rule) : Gate → Prop
  | .seq U V => Fits P R U ∧ Fits P R V
  | .adj U => Fits P R U
  | .SignedPhaseProd _ x z => SiteFits P R x z
  | .CSignedPhaseProd _ _ x z => SiteFits P R x z
  | _ => True

/-! ## The claims -/

section

variable (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsFacts qs] [LowerGateClass qs]

/-- **The conditional pass keeps the lowering's workspace**, on any layout. -/
def BalanceOK (P : ShorLoweringPolicy) (R : Rule) : Prop :=
  ∀ G : Gate, Policy.GateWorkspaceOK P G → Policy.GateWorkspaceOK P (balance P R G)

/-- **The conditional pass is correct**: lowering `balance P R G` with
`Policy.lowerGate` implements `G`, under `G`'s own preconditions. -/
def BalanceCorrect (P : ShorLoweringPolicy) (R : Rule) : Prop :=
  P.Admissible →
  ∀ (G : Gate) (hw : Policy.GateWorkspaceOK P G) (hb : Policy.GateWorkspaceOK P (balance P R G))
    (ψ : qs.State), Policy.GateWorkspaceCleanState qs P G hw ψ →
    LowerGateClass.evalL (qs := qs) (Policy.lowerGate P (balance P R G) hb) ψ = qs.eval G ψ

/-- **The unconditional pass keeps the lowering's workspace** where every site's
plan fits. -/
def BalanceUOK (P : ShorLoweringPolicy) (R : Rule) : Prop :=
  ∀ G : Gate, Policy.GateWorkspaceOK P G → Fits P R G → Policy.GateWorkspaceOK P (balanceU R G)

/-- **The unconditional pass is correct** where every site's plan fits: lowering
`balanceU R G` implements `G`, under `G`'s own preconditions. -/
def BalanceUCorrect (P : ShorLoweringPolicy) (R : Rule) : Prop :=
  P.Admissible →
  ∀ (G : Gate) (hw : Policy.GateWorkspaceOK P G) (_hf : Fits P R G)
    (hb : Policy.GateWorkspaceOK P (balanceU R G)) (ψ : qs.State),
    Policy.GateWorkspaceCleanState qs P G hw ψ →
    LowerGateClass.evalL (qs := qs) (Policy.lowerGate P (balanceU R G) hb) ψ = qs.eval G ψ

end

/-- **The default rule's plan fits** whenever the operands' spare qubits hold its
`siteNeed`. The reference layout is sized to this, so `balanceU` with the default
rule is sound on it. -/
def DefaultRuleFits (P : ShorLoweringPolicy) : Prop :=
  ∀ x z : ExtReg,
    (siteNeed P defaultRule x.width z.width).1 ≤ x.capacity →
    (siteNeed P defaultRule x.width z.width).2 ≤ z.capacity →
    SiteFits P defaultRule x z

/-! ### Shor's circuit after each pass

`ShorCorrectApproxLoweredUniform` (`Shor/Statement.lean`) for the circuit lowered
after each pass: on any registers ready for Shor, the lowering keeps the ideal
bound `κ / log(log₂ N + 1)` up to the approximation loss, for some `K ≤ 1600`.
The circuits are stated over any workspace proof `hb`, which by proof irrelevance
does not change them. -/

section

variable (qs : QSemantics) [RegEncoding qs.Basis] [MeasureClass qs] [GateSemanticsFacts qs]
  [LowerGateClass qs]

/-- **Shor's circuit lowered after the conditional pass is correct**, on any
registers ready for Shor. -/
def BalancedShorCorrect (R : Rule) : Prop :=
  ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
  ∃ K : ℝ, 0 ≤ K ∧ K ≤ 1600 ∧
    ∀ (inst : ShorOrderFindingInstance) (P : ShorLoweringPolicy) (_hP : P.Admissible)
      (x y work scratch : ExtReg) (flag : ℕ) (b0 : qs.Basis)
      (_hm : regSize x.active = Nat.log2 (2 * inst.N^2))
      (_hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
      (hready : LoweredShorReady qs P η inst.a inst.N x y work scratch flag b0)
      (hb : Policy.GateWorkspaceOK P (balance P R hready.circuit)),
      probability_of_success (qs := qs) (T := T)
        (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
        (x := x.active) (r := ord inst.a inst.N inst.coprime) (Q := ASize x.active)
        (evalC := LowerGateClass.evalL (qs := qs))
        (C := Policy.lowerGate P (balance P R hready.circuit) hb) (ψ := qs.ket b0)
      ≥ κ / Real.log ((Nat.log2 inst.N : ℝ) + 1)
        - 2 * (regSize x.active : ℝ) * Real.sqrt (2 * (K * η))

/-- **Shor's circuit lowered after the unconditional pass is correct**, on any
registers ready for Shor whose sites all fit. -/
def BalancedUShorCorrect (R : Rule) : Prop :=
  ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
  ∃ K : ℝ, 0 ≤ K ∧ K ≤ 1600 ∧
    ∀ (inst : ShorOrderFindingInstance) (P : ShorLoweringPolicy) (_hP : P.Admissible)
      (x y work scratch : ExtReg) (flag : ℕ) (b0 : qs.Basis)
      (_hm : regSize x.active = Nat.log2 (2 * inst.N^2))
      (_hn : regSize y.active = Nat.log2 (2 * inst.N)) (η : ℝ)
      (hready : LoweredShorReady qs P η inst.a inst.N x y work scratch flag b0)
      (_hf : Fits P R hready.circuit)
      (hb : Policy.GateWorkspaceOK P (balanceU R hready.circuit)),
      probability_of_success (qs := qs) (T := T)
        (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
        (x := x.active) (r := ord inst.a inst.N inst.coprime) (Q := ASize x.active)
        (evalC := LowerGateClass.evalL (qs := qs))
        (C := Policy.lowerGate P (balanceU R hready.circuit) hb) (ψ := qs.ket b0)
      ≥ κ / Real.log ((Nat.log2 inst.N : ℝ) + 1)
        - 2 * (regSize x.active : ℝ) * Real.sqrt (2 * (K * η))

end

end Balanced
end Shor
