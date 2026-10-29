import FastMultiplication.ShorVerification.Implementation.Shor.Lowering.LowerGate

/-!
# Balanced phase products for unequal operands: definitions

ForShor splits both operands of a phase product at one common limb width
`phaseLimbWidth x z k = min (x.width / k) (z.width / k)`, so at an unequal site
the larger operand's top chunk takes the whole remainder and fixes the child
width (Step 4 at `n = 2048`: `2348 × 4399`, child `2849` at `k = 3`).

This leaf module adds a *gate-level* balancing pass that runs before the
existing lowering and leaves ForShor's proved equal-width core untouched:

* `splitGate` cuts the larger operand `x` into blocks: lower blocks of width
  `w` (read unsigned; they are zero-extended by at least one bit) and a signed
  top block. Every block is multiplied by the whole small operand with an
  ordinary ForShor phase product, each block pair first extended to a common
  target width `t` (zero extension for a lower block, sign extension for the
  top block and for the small operand). The phases add:
  `φ·x·z = Σ_b (φ·2^{offset_b})·x_b·z`.
* A plan with no lower blocks is plain padding of the small operand to a
  common width (candidate (b)); a plan with lower blocks is the recursive
  rebalancing (candidate (c)). Both are instances of one construction.
* `siteGate` applies a plan only when a decidable check `fitsB` says the
  operands' *existing* reserves cover every block (`Policy.reserveNeed`, i.e.
  whatever child-width rule ForShor's core uses), otherwise it keeps the
  original gate. So balancing never needs a bigger layout than the one the
  original site was proved ready on.
* `balance` applies `siteGate` at every signed / controlled signed phase
  product of a circuit (through `seq` and `adj`).

Widths enter only through two parameters: the plan rule `Rule` (block widths
and targets as a function of the two operand widths) and the core's reserve
function `Policy.reserveNeed P` (which is where the child/working width rule
lives). Neither is fixed here.
-/

namespace Shor
namespace Balanced

open Gate

/-! ## Block registers -/

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

@[simp] theorem lowBlock_reserve (x : ExtReg) (w : ℕ) : (lowBlock x w).reserve = x.reserve := rfl
@[simp] theorem highPart_reserve (x : ExtReg) (w : ℕ) : (highPart x w).reserve = x.reserve := rfl

@[simp] theorem lowBlock_capacity (x : ExtReg) (w : ℕ) : (lowBlock x w).capacity = x.capacity := rfl
@[simp] theorem highPart_capacity (x : ExtReg) (w : ℕ) : (highPart x w).capacity = x.capacity := rfl

theorem lowBlock_width (x : ExtReg) (w : ℕ) (hw : w ≤ x.width) : (lowBlock x w).width = w := by
  simp [lowBlock, ExtReg.width, regSize, Reg.width, Reg.take] at hw ⊢
  omega

theorem highPart_width (x : ExtReg) (w : ℕ) : (highPart x w).width = x.width - w := by
  simp [highPart, ExtReg.width, regSize, Reg.width, Reg.drop]

/-! ## Controlled or uncontrolled product leaves -/

/-- Which phase-product gate a block uses: the site's own kind. -/
inductive Ctl
  | none
  | ctrl (q : ℕ)
  deriving DecidableEq

/-- The phase-product gate of kind `c`. -/
def Ctl.gate : Ctl → Angle → ExtReg → ExtReg → Gate
  | .none, φ, x, z => Gate.SignedPhaseProd φ x z
  | .ctrl q, φ, x, z => Gate.CSignedPhaseProd q φ x z

/-! ## Plans -/

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

/-! ## The balanced gate -/

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

/-! ## The decidable fit check -/

/-- Every block of the plan is well formed and the operands' existing reserves
cover every block product (its extension bits plus `Policy.reserveNeed` at the
block's common width). -/
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

theorem fitsB_nil {P : ShorLoweringPolicy} {t : ℕ} {x z : ExtReg} :
    fitsB P [] t x z = true ↔
      x.width ≤ t ∧ z.width ≤ t ∧
      (t - x.width) + (Policy.reserveNeed P t t).1 ≤ x.capacity ∧
      (t - z.width) + (Policy.reserveNeed P t t).2 ≤ z.capacity := by
  simp [fitsB, and_assoc]

theorem fitsB_cons {P : ShorLoweringPolicy} {b : Block} {bs : List Block} {t : ℕ} {x z : ExtReg} :
    fitsB P (b :: bs) t x z = true ↔
      b.w < x.width ∧ b.w + 1 ≤ b.t ∧ z.width ≤ b.t ∧
      (b.t - b.w) + (Policy.reserveNeed P b.t b.t).1 ≤ x.capacity ∧
      (b.t - z.width) + (Policy.reserveNeed P b.t b.t).2 ≤ z.capacity ∧
      fitsB P bs t (highPart x b.w) z = true := by
  simp [fitsB, and_assoc]

/-! ## The site rewrite and the pass -/

/-- Balance one phase-product site of kind `c`: split the wider operand with the
rule's plan when it fits the existing reserves; otherwise keep the site. -/
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

/-- The balancing pass: every signed / controlled signed phase product becomes
its `siteGate`. QFTs are left alone (their twiddle sites differ by at most one
bit and are lowered inside `Policy.lowerQFT`). -/
def balance (P : ShorLoweringPolicy) (R : Rule) : Gate → Gate
  | .seq U V => .seq (balance P R U) (balance P R V)
  | .adj U => .adj (balance P R U)
  | .SignedPhaseProd φ x z => siteGate P R .none φ x z
  | .CSignedPhaseProd q φ x z => siteGate P R (.ctrl q) φ x z
  | G => G

/-! ## The default rule

The rule the cost study selected at `n = 2048` (inquiry/EVIDENCE_CARD.md):
with `s` the small width and `L > s` the big one,

* `2L ≤ 3s`: pad the small operand to `L` (no lower block);
* otherwise `B = ⌈L / s⌉` blocks: `B - 1` lower blocks of width `s - 1`
  (one zero bit makes them `s` wide) and the top block, every product at
  the common width `max s top`.

At `n = 2048` this reproduces the searched optimum for the STO reference policy
under both width rules. -/
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

end Balanced
end Shor
