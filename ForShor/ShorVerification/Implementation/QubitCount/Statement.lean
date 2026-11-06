import ForShor.ShorVerification.Framework.Gatecount.ResourceModel
import ForShor.ShorVerification.Implementation.Compiler.Statement
import ForShor.ShorVerification.Implementation.Reference.Balanced.Main

/-!
# Qubit count: definitions and claims

Everything needed to state what `Main.lean` proves. Nothing here imports
another file of this folder.

**What is counted.** A lowered circuit is walked in time order while a set of
*live* physical qubits is maintained. A gate makes the qubits it acts on live;
an extension makes the reserve qubits it activates live; a deallocation
returns the qubits it releases. The peak is the largest size the live set
reaches. An adjoint walks its body backwards, and in that direction an
extension releases and a deallocation activates.

**Scratch.** `AddScaled` and `Negate` also use clean scratch qubits that have
no index in the circuit. While such a primitive runs, the count adds the
scratch `shorGateResourceModel` charges it (`cleanAnc`): one qubit for
`AddScaled`, the register width plus one for `Negate`.

**What is claimed.** For the lowered order-finding circuit, started with its
registers live, the peak, scratch included, is the width of those registers
plus a budget computed from the register widths and the lowering policy by
plain arithmetic on fuel. Each table is read once, into the map that gives
every slot's largest width as a max-plus function of the initial chunk
widths; a phase product then costs one recursion chain of `log_k w` levels,
each a few additions and comparisons, and a QFT the largest split over the
two widths at each depth of its halving tree. The same holds after `Balanced.balance`, with each
phase-product site costed as the split or the product it runs.
-/

namespace Shor

/-! =========================================================
    The live-set walk
========================================================= -/

namespace QubitCount

/-- The physical qubits an extension by `n` activates, and that the matching
deallocation releases: the first `n` reserve qubits of `r`. -/
def allocBits (r : ExtReg) (n : ℕ) : Finset ℕ :=
  regQubitSet (r.newBits n)

/-- The live set after activating (`true`) or releasing (`false`) `B`. -/
def move (activate : Bool) (B L : Finset ℕ) : Finset ℕ :=
  if activate then L ∪ B else L \ B

/-- The live set after a gate, walked forwards (`true`) or backwards (`false`). -/
def after : LowGate → Bool → Finset ℕ → Finset ℕ
  | .id, _, L => L
  | .seq U V, true, L => after V true (after U true L)
  | .seq U V, false, L => after U false (after V false L)
  | .adj U, d, L => after U (!d) L
  | .H q, _, L => L ∪ LowGate.usedQubits (.H q)
  | .X q, _, L => L ∪ LowGate.usedQubits (.X q)
  | .Phase q a, _, L => L ∪ LowGate.usedQubits (.Phase q a)
  | .CNOT c t, _, L => L ∪ LowGate.usedQubits (.CNOT c t)
  | .Toffoli c₁ c₂ t, _, L => L ∪ LowGate.usedQubits (.Toffoli c₁ c₂ t)
  | .ShiftL r n, _, L => L ∪ LowGate.usedQubits (.ShiftL r n)
  | .ShiftR r n, _, L => L ∪ LowGate.usedQubits (.ShiftR r n)
  | .Negate r, _, L => L ∪ LowGate.usedQubits (.Negate r)
  | .AddScaled dst src s k, _, L => L ∪ LowGate.usedQubits (.AddScaled dst src s k)
  | .RadixReverse r m, _, L => L ∪ LowGate.usedQubits (.RadixReverse r m)
  | .zeroExtend r n, d, L => move d (allocBits r n) L
  | .signExtend r n, d, L => move d (allocBits r n) L
  | .zeroDealloc r n, d, L => move (!d) (allocBits r n) L
  | .signDealloc r n, d, L => move (!d) (allocBits r n) L

/-- The largest live-set size reached while walking a gate, with `anc g` extra
qubits charged while the primitive `g` runs. -/
def peak (anc : LowGate → ℕ) : LowGate → Bool → Finset ℕ → ℕ
  | .id, _, L => L.card
  | .seq U V, true, L => max (peak anc U true L) (peak anc V true (after U true L))
  | .seq U V, false, L => max (peak anc V false L) (peak anc U false (after V false L))
  | .adj U, d, L => peak anc U (!d) L
  | .H q, _, L => (L ∪ LowGate.usedQubits (.H q)).card + anc (.H q)
  | .X q, _, L => (L ∪ LowGate.usedQubits (.X q)).card + anc (.X q)
  | .Phase q a, _, L => (L ∪ LowGate.usedQubits (.Phase q a)).card + anc (.Phase q a)
  | .CNOT c t, _, L => (L ∪ LowGate.usedQubits (.CNOT c t)).card + anc (.CNOT c t)
  | .Toffoli c₁ c₂ t, _, L =>
      (L ∪ LowGate.usedQubits (.Toffoli c₁ c₂ t)).card + anc (.Toffoli c₁ c₂ t)
  | .ShiftL r n, _, L => (L ∪ LowGate.usedQubits (.ShiftL r n)).card + anc (.ShiftL r n)
  | .ShiftR r n, _, L => (L ∪ LowGate.usedQubits (.ShiftR r n)).card + anc (.ShiftR r n)
  | .Negate r, _, L => (L ∪ LowGate.usedQubits (.Negate r)).card + anc (.Negate r)
  | .AddScaled dst src s k, _, L =>
      (L ∪ LowGate.usedQubits (.AddScaled dst src s k)).card + anc (.AddScaled dst src s k)
  | .RadixReverse r m, _, L =>
      (L ∪ LowGate.usedQubits (.RadixReverse r m)).card + anc (.RadixReverse r m)
  | .zeroExtend r n, d, L => max L.card (move d (allocBits r n) L).card
  | .signExtend r n, d, L => max L.card (move d (allocBits r n) L).card
  | .zeroDealloc r n, d, L => max L.card (move (!d) (allocBits r n) L).card
  | .signDealloc r n, d, L => max L.card (move (!d) (allocBits r n) L).card

/-- The clean scratch qubits the resource model charges to `u` while it runs. -/
def scratch (u : LowGate) : ℕ :=
  (LowGate.resources shorGateResourceModel u).cleanAnc

end QubitCount

namespace LowGate

/-- The peak number of live qubits while `g` runs from the live set `L`,
scratch included. -/
def peakQubits (g : LowGate) (L : Finset ℕ) : ℕ :=
  QubitCount.peak QubitCount.scratch g true L

end LowGate

/-! =========================================================
    The budgets
========================================================= -/

/-- The largest value of `f` over `Fin k`, with `⊥` for no slot. -/
def supBot : (k : ℕ) → (Fin k → WithBot ℤ) → WithBot ℤ
  | 0, _ => ⊥
  | k + 1, f => f 0 ⊔ supBot k fun i => f i.succ

/-- `⊥` to `0`, otherwise the integer clamped at `0`. -/
def botToNat (x : WithBot ℤ) : ℕ := (x.unbotD 0).toNat

/-- The chunk widths of operands of widths `xw` and `zw` split `k` ways:
`k - 1` limbs of width `min (xw / k) (zw / k)` and a top chunk with the rest. -/
def initWidths (k xw zw : ℕ) : WidthState k :=
  let ℓ := min (xw / k) (zw / k)
  { xw := fun i => phaseSplitLogicalWidth xw ℓ k i
    zw := fun i => phaseSplitLogicalWidth zw ℓ k i }

/-! ---------------------------------------------------------
    The width map of a table
--------------------------------------------------------- -/

/-- A slot width as a function of the initial slot widths: the largest of
`init s + coef s` over the slots `s` and of `const`, with `⊥` for an absent
term. -/
structure WidthTerm (k : ℕ) where
  coef : Fin k → WithBot ℤ
  const : WithBot ℤ

namespace WidthTerm

variable {k : ℕ}

/-- The initial width of slot `s`. -/
def var (s : Fin k) : WidthTerm k :=
  ⟨fun t => if t = s then ((0 : ℤ) : WithBot ℤ) else ⊥, ⊥⟩

/-- `e + c`. -/
def add (e : WidthTerm k) (c : ℤ) : WidthTerm k :=
  ⟨fun t => e.coef t + (c : WithBot ℤ), e.const + (c : WithBot ℤ)⟩

/-- `max e f`. -/
def sup (e f : WidthTerm k) : WidthTerm k :=
  ⟨fun t => e.coef t ⊔ f.coef t, e.const ⊔ f.const⟩

/-- `max (e - n) 0`. -/
def trunc (e : WidthTerm k) (n : ℕ) : WidthTerm k :=
  ⟨fun t => e.coef t + ((-(n : ℤ) : ℤ) : WithBot ℤ),
   (e.const + ((-(n : ℤ) : ℤ) : WithBot ℤ)) ⊔ ((0 : ℤ) : WithBot ℤ)⟩

/-- The width at the initial slot widths `init`. -/
def eval (e : WidthTerm k) (init : Fin k → ℕ) : WithBot ℤ :=
  supBot k (fun s => e.coef s + (((init s : ℕ) : ℤ) : WithBot ℤ)) ⊔ e.const

/-- `e` with its coefficients stored. -/
def norm (e : WidthTerm k) : WidthTerm k :=
  let l := List.ofFn e.coef
  ⟨fun t => l.get (Fin.cast List.length_ofFn.symm t), e.const⟩

end WidthTerm

/-- The terms of the `k` slots, stored. -/
structure Slots (k : ℕ) where
  get : Fin k → WidthTerm k

/-- `E` with its terms stored. -/
def Slots.ofFn {k : ℕ} (E : Fin k → WidthTerm k) : Slots k :=
  let l := List.ofFn fun i => (E i).norm
  ⟨fun i => l.get (Fin.cast List.length_ofFn.symm i)⟩

open Operations in
/-- One table operation on the slot widths, as `updateWidthState` acts on
them. -/
def symUpdate {k : ℕ} (S : Slots k) : valid_ops k → Slots k
  | .shiftL i n => .ofFn (Function.update S.get i ((S.get i).add n))
  | .shiftR i n => .ofFn (Function.update S.get i ((S.get i).trunc n))
  | .negate i => .ofFn (Function.update S.get i ((S.get i).add 1))
  | .addScaled dst src _ sh =>
      .ofFn (Function.update S.get dst (((S.get dst).sup ((S.get src).add sh)).add 1))
  | .phaseProduct _ => S

/-- The largest width each slot reaches over a program, from the current
widths `cur` and the largest so far `mx`. -/
def symScanAux {k : ℕ} (cur mx : Slots k) : List (Operations.valid_ops k) → Slots k
  | [] => mx
  | op :: rest =>
      let cur' := symUpdate cur op
      symScanAux cur' (.ofFn fun i => (mx.get i).sup (cur'.get i)) rest

/-- The width map of a table: the largest width each slot reaches over the
program, in terms of the initial slot widths. -/
def widthMap {k : ℕ} (ops : Prog k) : Slots k :=
  symScanAux ⟨WidthTerm.var⟩ ⟨WidthTerm.var⟩ ops

/-- What the budgets read off a table: its width map, which operations it
has, and for the exact width rule its program. -/
structure TableData where
  k : ℕ
  ops : Prog k
  map : Slots k
  negates : Bool
  adds : Bool

open Operations in
/-- A table's data, by one pass over its program. -/
def ToomCookTable.compile (T : ToomCookTable) : TableData :=
  ⟨T.k, T.ops, widthMap T.ops,
   T.ops.any fun op => match op with | .negate _ => true | _ => false,
   T.ops.any fun op => match op with | .addScaled _ _ _ _ => true | _ => false⟩

/-- The policy's bands, each table compiled. -/
def Policy.compile (P : ShorLoweringPolicy) : List (ℕ × TableData) :=
  P.bands.map fun b => (b.threshold, b.table.compile)

/-- The data of the table a policy uses at width `n`: the first band whose
threshold is `≤ n`. -/
def chooseData (D : List (ℕ × TableData)) (n : ℕ) : Option TableData :=
  (D.find? fun b => decide (b.1 ≤ n)).map Prod.snd

/-- The largest scratch a table's arithmetic charges on chunks of width `W`. -/
def TableData.scratch (d : TableData) (W : ℕ) : ℕ :=
  if d.negates then 1 else if d.adds then 1 else 0

/-- The common width of the next recursion level: under the scan rule one
above the largest slot width the table's map gives at `initWidths`, under the
exact rule `exactSignedWidthOfWidths`. -/
def TableData.levelWidth (d : TableData) (R : WidthRule) (xw zw : ℕ) : ℕ :=
  match R with
  | .scan =>
      let init := initWidths d.k xw zw
      1 + botToNat (supBot d.k fun i => (d.map.get i).eval init.xw ⊔ (d.map.get i).eval init.zw)
  | .exact => exactSignedWidthOfWidths d.ops xw zw

/-! ---------------------------------------------------------
    The budgets of compiled tables
--------------------------------------------------------- -/

/--
Peak extra qubits of one lowered signed phase product on operands of widths
`wx` and `wz`, by fuel. A recursive level grows its `k` chunk pairs to the
next width `W`, activating `k·W - wx` and `k·W - wz` qubits, and then holds
the larger of one child's peak and its arithmetic's scratch. The chain stops
where the policy has no table or the width stops shrinking.
-/
def peakReserveF (R : WidthRule) (D : List (ℕ × TableData)) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | f + 1, wx, wz =>
    match chooseData D (max wx wz) with
    | none => 0
    | some d =>
      let W := d.levelWidth R wx wz
      if W < max wx wz then
        (d.k * W - wx) + (d.k * W - wz) + max (peakReserveF R D f W W) (d.scratch W)
      else 0

/-- `peakReserveF` with fuel for the whole chain. -/
def peakReserveD (R : WidthRule) (D : List (ℕ × TableData)) (wx wz : ℕ) : ℕ :=
  peakReserveF R D (max wx wz + 1) wx wz

/-- The reserve `(x side, z side)` the allocator gives a phase product, by
fuel: each level's growth plus `k` full children. -/
def reserveBudgetF (R : WidthRule) (D : List (ℕ × TableData)) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, _, _ => (0, 0)
  | f + 1, wx, wz =>
    match chooseData D (max wx wz) with
    | none => (0, 0)
    | some d =>
      let W := d.levelWidth R wx wz
      if W < max wx wz then
        let child := reserveBudgetF R D f W W
        ((d.k * W - wx) + d.k * child.1, (d.k * W - wz) + d.k * child.2)
      else (0, 0)

/-- `reserveBudgetF` with fuel for the whole chain. -/
def reserveBudgetD (R : WidthRule) (D : List (ℕ × TableData)) (wx wz : ℕ) : ℕ × ℕ :=
  reserveBudgetF R D (max wx wz + 1) wx wz

/-- The extra qubits of one QFT split of width `m`: its phase product on the
two halves each grown by one qubit. -/
def qftSplitPeak (pp : ℕ → ℕ → ℕ) (m : ℕ) : ℕ :=
  if 2 ≤ m then 2 + pp (m / 2 + 1) (m - m / 2 + 1) else 0

/-- The largest split peak down the QFT's halving tree, whose widths at depth
`j` are `lo = ⌊n / 2^j⌋` and `hi = ⌈n / 2^j⌉`. -/
def qftPeakF (pp : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | f + 1, lo, hi =>
      max (max (qftSplitPeak pp lo) (qftSplitPeak pp hi))
        (if 2 ≤ hi then qftPeakF pp f (lo / 2) ((hi + 1) / 2) else 0)

/-- Peak extra qubits of the lowered QFT on `n` qubits. -/
def qftPeakD (R : WidthRule) (D : List (ℕ × TableData)) (n : ℕ) : ℕ :=
  qftPeakF (peakReserveD R D) (n + 1) n n

/--
Peak extra qubits of each phase of one controlled modular multiplication, over
the exponent, data with its carry bit, work, scratch and flag qubits, for data
width `dW` and spare capacity `dC`, work width `wW` and spare capacity `wC`,
and scratch width `sW` and spare capacity `sC`, when a phase product on
widths `wx`, `wz` and spare capacities `cx`, `cz` peaks `pp wx cx wz cz` and
a QFT on `n` qubits peaks `qp n`:

1. Step 1's phase product, between the data and work registers.
2. The QFT on the work register.
3. Step 2's QFTs on the data register with its carry bit.
4. Step 2's phase product, between the work register and the data register
   with its carry bit.
5. Step 3's constant comparison and subtraction on the scratch register: one
   unit qubit, two qubits of arithmetic scratch (swap 001: the negation is the
   incrementer, one clean ancilla, not a register-wide constant).
6. Step 4's QFTs on the scratch register.
7. Step 4's phase product, between the work and scratch registers.
8. Step 5's phase product, between the data register with its carry bit and
   the work register.

Every phase product runs on its operands each grown by one qubit.
-/
def modMulPhasePeaksWith (pp : ℕ → ℕ → ℕ → ℕ → ℕ) (qp : ℕ → ℕ)
    (dW dC wW wC sW sC : ℕ) : List ℕ :=
  [ 2 + pp (dW + 1) (dC - 2) (wW + 1) (wC - 1)
  , qp wW
  , qp (dW + 1)
  , 2 + pp (wW + 1) (wC - 1) (dW + 2) (dC - 2)
  , 3
  , qp sW
  , 2 + pp (wW + 1) (wC - 1) (sW + 1) (sC - 1)
  , 2 + pp (dW + 2) (dC - 2) (wW + 1) (wC - 1) ]

/-- Peak extra qubits of one controlled modular multiplication. -/
def modMulPeakWith (pp : ℕ → ℕ → ℕ → ℕ → ℕ) (qp : ℕ → ℕ) (dW dC wW wC sW sC : ℕ) : ℕ :=
  (modMulPhasePeaksWith pp qp dW dC wW wC sW sC).foldr max 0

/-- Peak extra qubits of the order-finding circuit: the multiplications, if
there are any, and the final inverse QFT on the exponent register. -/
def orderFindingPeakWith (pp : ℕ → ℕ → ℕ → ℕ → ℕ) (qp : ℕ → ℕ)
    (xW dW dC wW wC sW sC : ℕ) : ℕ :=
  max (if 0 < xW then modMulPeakWith pp qp dW dC wW wC sW sC else 0) (qp xW)

/-- Peak extra qubits of the order-finding circuit, phase products lowered
directly. -/
def orderFindingPeakD (R : WidthRule) (D : List (ℕ × TableData)) (xW dW wW sW : ℕ) : ℕ :=
  orderFindingPeakWith (fun wx _ wz _ => peakReserveD R D wx wz) (qftPeakD R D) xW dW 0 wW 0 sW 0

/-! ---------------------------------------------------------
    Balanced phase products
--------------------------------------------------------- -/

/-- Peak extra qubits of a balanced split (`Balanced.splitGate`) of an operand
of width `wx` against one of width `wz`: each block extends itself and the
small operand to its common width and runs one product there, returning what
it activated before the next block starts. -/
def splitPeakOf (pp : ℕ → ℕ → ℕ) : List Balanced.Block → ℕ → ℕ → ℕ → ℕ
  | [], t, wx, wz => (t - wx) + (t - wz) + pp t t
  | b :: bs, t, wx, wz =>
      max ((b.t - b.w) + (b.t - wz) + pp b.t b.t) (splitPeakOf pp bs t (wx - b.w) wz)

/-- `Balanced.fitsB` on widths and capacities, with the reserve `rn t t` a
block product at width `t` asks for. -/
def planFitsOf (rn : ℕ → ℕ → ℕ × ℕ) :
    List Balanced.Block → ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | [], t, wx, cx, wz, cz =>
      decide (wx ≤ t) && decide (wz ≤ t) &&
      decide ((t - wx) + (rn t t).1 ≤ cx) &&
      decide ((t - wz) + (rn t t).2 ≤ cz)
  | b :: bs, t, wx, cx, wz, cz =>
      decide (b.w < wx) && decide (b.w + 1 ≤ b.t) && decide (wz ≤ b.t) &&
      decide ((b.t - b.w) + (rn b.t b.t).1 ≤ cx) &&
      decide ((b.t - wz) + (rn b.t b.t).2 ≤ cz) &&
      planFitsOf rn bs t (wx - b.w) cx wz cz

/-- Peak extra qubits of a balanced phase-product site (`Balanced.siteGate`)
on widths `wx`, `wz` and spare capacities `cx`, `cz`: the split when the
widths differ and the rule's plan for the wider operand fits the capacities,
the product itself otherwise. -/
def sitePeakOf (pp : ℕ → ℕ → ℕ) (rn : ℕ → ℕ → ℕ × ℕ) (R : Balanced.Rule)
    (wx cx wz cz : ℕ) : ℕ :=
  if wz < wx then
    match R.plan wx wz with
    | some p =>
        if planFitsOf rn p.lower p.top wx cx wz cz then splitPeakOf pp p.lower p.top wx wz
        else pp wx wz
    | none => pp wx wz
  else if wx < wz then
    match R.plan wz wx with
    | some p =>
        if planFitsOf rn p.lower p.top wz cz wx cx then splitPeakOf pp p.lower p.top wz wx
        else pp wx wz
    | none => pp wx wz
  else pp wx wz

/-- `sitePeakOf` with the budgets of compiled tables. -/
def sitePeakD (R : WidthRule) (D : List (ℕ × TableData)) (Rule : Balanced.Rule)
    (wx cx wz cz : ℕ) : ℕ :=
  sitePeakOf (peakReserveD R D) (reserveBudgetD R D) Rule wx cx wz cz

/-- Peak extra qubits of the order-finding circuit after `Balanced.balance`
with the rule `Rule`, for registers of the given widths and spare capacities. -/
def orderFindingPeakBalancedD (R : WidthRule) (D : List (ℕ × TableData)) (Rule : Balanced.Rule)
    (xW dW dC wW wC sW sC : ℕ) : ℕ :=
  orderFindingPeakWith (sitePeakD R D Rule) (qftPeakD R D) xW dW dC wW wC sW sC

/-- Peak extra qubits of a balanced site from the widths alone: the split's peak
wherever the rule has a plan, the product's otherwise. -/
def sitePeakU (pp : ℕ → ℕ → ℕ) (Rule : Balanced.Rule) (wx wz : ℕ) : ℕ :=
  if wz < wx then
    match Rule.plan wx wz with
    | some p => splitPeakOf pp p.lower p.top wx wz
    | none => pp wx wz
  else if wx < wz then
    match Rule.plan wz wx with
    | some p => splitPeakOf pp p.lower p.top wz wx
    | none => pp wx wz
  else pp wx wz

/-- Peak extra qubits of the order-finding circuit after `Balanced.balanceU` with
the rule `Rule`, which splits every site, from the register widths alone. -/
def orderFindingPeakUD (R : WidthRule) (D : List (ℕ × TableData)) (Rule : Balanced.Rule)
    (xW dW wW sW : ℕ) : ℕ :=
  orderFindingPeakWith (fun wx _ wz _ => sitePeakU (peakReserveD R D) Rule wx wz) (qftPeakD R D)
    xW dW 0 wW 0 sW 0

/-! ---------------------------------------------------------
    The budgets of a policy
--------------------------------------------------------- -/

/-- Peak extra qubits of the order-finding circuit under the policy `P`,
phase products lowered directly. -/
def Policy.orderFindingPeak (P : ShorLoweringPolicy) (xW dW wW sW : ℕ) : ℕ :=
  orderFindingPeakD P.widthRule (Policy.compile P) xW dW wW sW

/-- Peak extra qubits of the balanced order-finding circuit under the policy
`P` and the rule `Rule`. -/
def Policy.orderFindingPeakBalanced (P : ShorLoweringPolicy) (Rule : Balanced.Rule)
    (xW dW dC wW wC sW sC : ℕ) : ℕ :=
  orderFindingPeakBalancedD P.widthRule (Policy.compile P) Rule xW dW dC wW wC sW sC

/-- **The qubit count of the lowered order-finding circuit**: its exponent
register, data register with carry bit, work and scratch registers and flag,
plus the extra qubits at the peak. -/
def Policy.orderFindingQubits (P : ShorLoweringPolicy) (xW dW wW sW : ℕ) : ℕ :=
  xW + (dW + 1) + wW + sW + 1 + Policy.orderFindingPeak P xW dW wW sW

/-- **The qubit count of the balanced order-finding circuit**, for registers of
the given widths and spare capacities. -/
def Policy.orderFindingQubitsBalanced (P : ShorLoweringPolicy) (Rule : Balanced.Rule)
    (xW dW dC wW wC sW sC : ℕ) : ℕ :=
  xW + (dW + 1) + wW + sW + 1 + Policy.orderFindingPeakBalanced P Rule xW dW dC wW wC sW sC

/-- Peak extra qubits of the unconditionally balanced order-finding circuit under
the policy `P` and the rule `Rule`. -/
def Policy.orderFindingPeakU (P : ShorLoweringPolicy) (Rule : Balanced.Rule) (xW dW wW sW : ℕ) :
    ℕ :=
  orderFindingPeakUD P.widthRule (Policy.compile P) Rule xW dW wW sW

/-- **The qubit count of the unconditionally balanced order-finding circuit**, from
the register widths alone. -/
def Policy.orderFindingQubitsU (P : ShorLoweringPolicy) (Rule : Balanced.Rule) (xW dW wW sW : ℕ) :
    ℕ :=
  xW + (dW + 1) + wW + sW + 1 + Policy.orderFindingPeakU P Rule xW dW wW sW

/-- The qubits that are live throughout the order-finding circuit: the
exponent register, the data register with its carry bit, the work and scratch
registers, and the flag. -/
def orderFindingBaseSet (x y work scratch : ExtReg) (flag : ℕ) : Finset ℕ :=
  regQubitSet x.active ∪ regQubitSet (y.grow 1).active ∪ regQubitSet work.active
    ∪ regQubitSet scratch.active ∪ {flag}

/-! =========================================================
    Hypotheses
========================================================= -/

/-- The register disjointness the order-finding claim needs beyond what the
workspace records of the circuit already state: the exponent register shares
no qubit with the data, work or scratch registers or the flag. -/
structure OrderFindingSpaceLayout (x y work scratch : ExtReg) (flag : ℕ) : Prop where
  exponent_data_disjoint : ExtReg.OwnedDisjoint x y
  exponent_work_disjoint : ExtReg.OwnedDisjoint x work
  exponent_scratch_disjoint : ExtReg.OwnedDisjoint x scratch
  flag_outside_exponent : flag ∉ x.ownedQubits

/-! =========================================================
    Claims
========================================================= -/

/--
**The qubit-count formula for the lowered order-finding circuit.** Started
with the exponent, data (with its carry bit), work and scratch registers and
the flag live, its peak, scratch included, is `orderFindingQubits`.
-/
def Policy.OrderFindingPeakFormula (P : ShorLoweringPolicy) : Prop :=
  P.Admissible →
  ∀ (a N : ℕ) (x y work scratch : ExtReg) (flag : ℕ)
    (hmod : ModMulCircuitWorkspaceOK y work)
    (hstep4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : Policy.GateWorkspaceOK P (orderFindingApprox a N x y work scratch flag hmod hstep4)),
    OrderFindingSpaceLayout x y work scratch flag →
    (orderFindingApproxLow P a N x y work scratch flag hmod hstep4 hws).peakQubits
        (orderFindingBaseSet x y work scratch flag)
      = Policy.orderFindingQubits P x.width y.width work.width scratch.width

/--
**The qubit-count formula for the balanced order-finding circuit.** Lowered
after `Balanced.balance` with the rule `R`, and started from the same live
set, its peak, scratch included, is `orderFindingQubitsBalanced` at the
registers' widths and spare capacities.
-/
def Policy.OrderFindingPeakFormulaBalanced (P : ShorLoweringPolicy) (R : Balanced.Rule) : Prop :=
  P.Admissible →
  ∀ (a N : ℕ) (x y work scratch : ExtReg) (flag : ℕ)
    (hmod : ModMulCircuitWorkspaceOK y work)
    (hstep4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : Policy.GateWorkspaceOK P (orderFindingApprox a N x y work scratch flag hmod hstep4)),
    OrderFindingSpaceLayout x y work scratch flag →
    (Balanced.orderFindingApproxLowBalanced P R a N x y work scratch flag hmod hstep4 hws).peakQubits
        (orderFindingBaseSet x y work scratch flag)
      = Policy.orderFindingQubitsBalanced P R x.width
          y.width y.capacity work.width work.capacity scratch.width scratch.capacity

/--
**The qubit-count formula for the unconditionally balanced order-finding
circuit.** Lowered after `Balanced.balanceU` with the rule `R`, which splits
every site, on registers whose spare qubits hold every site's plan
(`Balanced.Fits`), and started from the same live set, its peak, scratch
included, is `orderFindingQubitsU` at the registers' widths alone.
-/
def Policy.OrderFindingPeakFormulaBalancedU (P : ShorLoweringPolicy) (R : Balanced.Rule) : Prop :=
  P.Admissible →
  ∀ (a N : ℕ) (x y work scratch : ExtReg) (flag : ℕ)
    (hmod : ModMulCircuitWorkspaceOK y work)
    (hstep4 : CmpLtNWWorkspace N (y.grow 1) work scratch flag)
    (hws : Policy.GateWorkspaceOK P (orderFindingApprox a N x y work scratch flag hmod hstep4))
    (hf : Balanced.Fits P R (orderFindingApprox a N x y work scratch flag hmod hstep4)),
    OrderFindingSpaceLayout x y work scratch flag →
    (Balanced.orderFindingApproxLowBalancedU P R a N x y work scratch flag hmod hstep4 hws hf).peakQubits
        (orderFindingBaseSet x y work scratch flag)
      = Policy.orderFindingQubitsU P R x.width y.width work.width scratch.width

end Shor
