# `Implementation/QubitCount/`

This folder defines how many qubits a lowered circuit needs at once and
proves an exact formula for that number for the lowered order-finding
circuit, with and without the balanced phase products of
`Reference/Balanced/`.

`Statement.lean` is the only file needed to see what is claimed: it holds
every definition the claims depend on and imports nothing else from this
folder. `Main.lean` proves the claims stated in `Statement.lean`; `Proofs/`
holds the lemmas those proofs use.

## Background

**What is counted.** A lowered circuit is walked in time order while a set of
*live* physical qubits is kept. A gate makes the qubits it acts on live. An
extension (`zeroExtend`, `signExtend`) makes the reserve qubits it activates
live. A deallocation (`zeroDealloc`, `signDealloc`) releases them. A live
qubit stays live while it waits, whether or not a gate acts on it. The peak
is the largest size the live set reaches. An adjoint walks its body
backwards, and in that direction an extension releases and a deallocation
activates.

**Scratch.** `AddScaled` and `Negate` also use clean scratch qubits that
have no index in the circuit: the carry of the Cuccaro adder, and the
constant-one register and carry of a negation. While such a primitive runs,
the count adds what `shorGateResourceModel` charges it (`cleanAnc`): one
qubit for `AddScaled`, the register width plus one for `Negate`. The scratch
is returned clean when the primitive ends, so sequential primitives reuse it.

**Why it differs from the footprint.** `LowGate.qubitCount` in
`Framework/Gatecount/ResourceModel.lean` counts every qubit the circuit ever
touches. The reserve budgets in `PhaseProduct/Statement.lean` give each of
the `k` children of a phase-product recursion its own slice of reserve,
although the children run one after another. The peak counts only what is
live together, so one child at a time.

**Two qubits the circuit uses without activating.** The data register's carry
bit is first acted on in Step 2 of a modular multiplication and never
released, so the formula counts it as part of the data register. Step 3's
constant arithmetic uses the scratch register's first reserve qubit without
activating it, so that qubit is live from Step 3 until Step 4's first QFT
activates and then releases it. The formula is exact with both.

## `Statement.lean`

**The live-set walk.** `QubitCount.after` and `QubitCount.peak` walk a
`LowGate` in either direction; `peak` charges `anc g` extra qubits while a
primitive `g` runs. `LowGate.peakQubits g L` is the peak from the live set
`L` with the resource model's scratch charge.

**The budgets.** Every budget is plain arithmetic on fuel, and each table is
read once.

- `WidthTerm k` is a slot width as a function of the `k` initial chunk
  widths: the largest of `init s + coef s` over the slots and of a constant,
  with `⊥` for an absent term. Every table operation acts on slot widths by
  `+ c`, `max`, or `max (· − n) 0`, so `symUpdate` carries terms through an
  operation and `widthMap ops` is each slot's largest width over the whole
  program, in terms of the initial widths. This is the one pass over a table.
- `ToomCookTable.compile` is a table's `TableData`: its `k`, its width map,
  whether it negates or adds, and its program (for the exact width rule).
  `TableData.scratch d W` is the largest scratch its arithmetic charges on
  chunks of width `W` (`W + 1` with a `negate`, 1 with an `addScaled`).
  `Policy.compile P` compiles each band; `chooseData` picks the band at a
  width.
- `TableData.levelWidth d R xw zw` is the common width of the next recursion
  level: under the scan rule one above the largest value of the width map at
  `initWidths`, a `k × k` max-plus product; under the exact rule
  `exactSignedWidthOfWidths`.
- `peakReserveD R D wx wz` is the peak extra qubits of one signed phase
  product. A level that recurses to width `W` activates `k·W − wx` and
  `k·W − wz` qubits, because its `k` chunks partition each operand, and then
  holds the larger of one child's peak and its arithmetic's scratch. The chain
  has one level per recursion, about `log_k w` of them.
- `reserveBudgetD R D wx wz` is the reserve the allocator asks for, the same
  chain with `k` children per level.
- `qftPeakD R D n` is the peak of the QFT: the largest split peak over its
  halving tree, which at depth `j` holds only the widths `⌊n / 2^j⌋` and
  `⌈n / 2^j⌉`, so two `peakReserveD` evaluations per depth.
- `modMulPhasePeaksWith pp qp` lists the extra qubits of the eight phases of
  one modular multiplication when a phase product costs `pp wx cx wz cz` and
  a QFT costs `qp n`; `orderFindingPeakWith pp qp` is the largest of those
  and the final inverse QFT. The scratch negations of Steps 3 and 4 give the
  entry `sW + 2`. `orderFindingPeakD R D` is it with `pp = peakReserveD R D`
  and `qp = qftPeakD R D`.
- `sitePeakD R D Rule wx cx wz cz` is the peak of a balanced site: the
  split's peak (`splitPeakOf`, the largest block's extension bits plus the
  product at its width `t`) when the rule's plan fits the operands' spare
  capacities (`planFitsOf`, which is `Balanced.fitsB` on widths and
  capacities), the product itself otherwise. `orderFindingPeakBalancedD` is
  `orderFindingPeakWith` with `pp = sitePeakD R D Rule`.
- `Policy.orderFindingPeak P` and `Policy.orderFindingPeakBalanced P Rule`
  are `orderFindingPeakD` and `orderFindingPeakBalancedD` at `P.widthRule`
  and `Policy.compile P`.

`orderFindingBaseSet` is the set the order-finding circuit starts from: the
exponent, data with carry bit, work and scratch registers, and the flag.

**Claims.** Every claim is stated with `peakQubits`, scratch included.

- `Policy.OrderFindingPeakFormula`: from `orderFindingBaseSet`, the peak of
  the lowered order-finding circuit is
  `xW + (dW + 1) + wW + sW + 1 + orderFindingPeak`, the width of the base set
  plus the extra qubits at the peak.
- `Policy.ReferencePeakFormula`: the same for the reference circuit of an
  instance, in the reference widths.
- `Reference2048Peak`, `Reference2048PeakExample`: the exact 2048-bit numbers
  below.
- `Policy.OrderFindingPeakFormulaBalanced P R`: the same formula for the
  order-finding circuit lowered after `Balanced.balance P R`, with
  `orderFindingPeakBalanced P R` at the registers' widths and spare
  capacities in place of `orderFindingPeak`. It has the hypotheses of
  `Policy.OrderFindingPeakFormula` and no others. The four sites have widths
  and spare capacities `(dW + 1, dC − 2) × (wW + 1, wC − 1)`,
  `(wW + 1, wC − 1) × (dW + 2, dC − 2)`, `(wW + 1, wC − 1) × (sW + 1, sC − 1)`
  and `(dW + 2, dC − 2) × (wW + 1, wC − 1)`: each operand is grown by one
  qubit, and Step 1's data operand leaves its carry bit to Step 2.
- `Reference2048PeakBalanced`: the balanced 2048-bit numbers below.

The claims assume an admissible policy. The assumption is used once: an
admissible table has `2k − 1` phase-product leaves, so a recursive level
always has a child.

## `Main.lean`

Proves each claim: `Policy.orderFinding_peak_formula`,
`Policy.reference_peak_formula`, `reference_2048_peak`,
`reference_2048_peak_example`, `Policy.orderFinding_peak_formula_balanced`
and `reference_2048_peak_balanced`. Each depends only on `propext`,
`Classical.choice` and `Quot.sound`.

## `Proofs/`

| file | what it proves |
|---|---|
| `Walk.lean` | `WellFormed` and `reach`; reversal, the scratch-charge bound, monotonicity, the reach bound |
| `Registers.lean` | Register facts as finite sets: growth, reserve slices, layout chunks |
| `GateWalk.lean` | A walk on plan gates with phase products opaque; circuits that only act on live qubits, with their largest scratch charge |
| `Budgets.lean` | `Policy.opsScratch`; the budgets in the walk's shape: `Rec.peakReserve` by well-founded recursion through the compiler's `nextWidthBy`, `Rec.qftPeakOf` over the whole halving tree, and the claims stated with them |
| `Level.lean` | One recursion level: allocations, arithmetic body with its scratch, deallocations |
| `PhaseProduct.lean` | The induction over lowering plans; the phase-product peaks |
| `Unsigned.lean` | The one-qubit growth wrapper of `PhaseProdUsing`, including a pre-live qubit |
| `QFT.lean` | The QFT by recursion on width, with a fresh pool or a pre-live first pool qubit; the QFT peak |
| `Lowering.lean` | A walk on all high-level gates, equal to the walk of `Policy.lowerGate`, with phase products costing any given `pc wx wz`; the constant arithmetic |
| `Blocks.lean` | Composable facts for Hadamard layers, the wrappers, the QFT, and the primitives, for any phase-product cost |
| `ModMul.lean` | The five steps of one controlled modular multiplication |
| `OrderFinding.lean` | The exponentiation, the order-finding circuit, the base set, the reference instance, with the budgets of `Budgets.lean` |
| `Balanced.lean` | Extensions by any number of qubits, the block products, the split, a balanced site in either branch; balancing changes the walk only at the phase products; the balanced formula with the budgets of `Budgets.lean` |
| `Arith.lean` | The budgets of `Statement.lean` equal those of `Budgets.lean`: the width map evaluates to the compiler's width scan, one level's growth is `k·W − w`, the QFT tree holds two widths per depth |
| `Formula.lean` | The claims of `Statement.lean` from `OrderFinding.lean`, `Balanced.lean` and `Arith.lean` |
| `Numerals.lean` | The 2048-bit widths and claims; the budget by `decide +kernel` |
| `BalancedNumerals.lean` | The four 2048-bit sites' peaks; the reference layout's spare qubits make every site split; the balanced 2048-bit claim |

## The 2048-bit numbers

`reference_2048_peak` and `reference_2048_peak_example` in `Main.lean` are
kernel-checked numerals for the reference circuit built from the
repository's standard `k = 2` table (`standardPolicy 2`) at the headline
precision level `m2048`. For every 2048-bit modulus the register widths are
data 2048, work 2347 and scratch 4398, and the exponent register has
`log₂(2N²)` qubits, which is 4095 or 4096. The peak from the five registers'
live qubits, scratch included, is then

| exponent register | base set | extra at peak | peak |
|---|---|---|---|
| 4096 qubits | 12,891 | 6,428 | **19,319** |
| 4095 qubits | 12,890 | 6,428 | **19,318** |

For `N = 2²⁰⁴⁸ − 1` the exponent register has 4096 qubits and the peak is
exactly 19,319. From an empty start the circuit never exceeds 19,319 qubits.
In both cases the peak is Step 4's phase product between the work and
scratch registers, at the deepest recursion level, while an `AddScaled` holds
its carry: 6,427 reserve qubits plus one scratch qubit. The negations of the
scratch register charge 4,399 scratch qubits, but run with about 12,900
qubits live, so they peak near 17,300.

The budget is evaluated by `decide +kernel` on `Policy.orderFindingPeak`
itself. Other tables give other numbers the same way: the table is read once
into its width map, and a phase product's chain is then one `k × k` max-plus
product per recursion level, about `log_k n` of them per site. Natively the
whole budget at 2048 bits takes milliseconds for the standard tables up to
`k = 7`.

The formula without scratch was checked against the real compiled circuit:
walking the JSON that `forshor_emit shor` prints, for eight instances with
`N` from 15 to 4,087 and `k` from 2 to 4, gave exactly that formula's peak
each time.

## The 2048-bit numbers, balanced

`reference_2048_peak_balanced` is the same reference circuit, same layout,
lowered after balancing every phase-product site with `Balanced.defaultRule`.
At the 2048-bit widths the rule pads Steps 1, 2 and 5 to 2348 × 2348 and
splits Step 4's 2348 × 4399 into two 2348 × 2348 products
(`Balanced/Checks.lean`). The reference layout gives each site at least the
spare qubits its unbalanced product needs, and that covers each plan; at
Steps 1, 2 and 5 exactly (for example `299 + 42,708 = 43,007`, the data side's
need at `2049 × 2348`). So every site splits. A 2348 × 2348 product peaks 257
above its start, so the sites cost

| site | balanced peak | unbalanced peak |
|---|---|---|
| Step 1, `2049 × 2348` | 2 + 299 + 257 = 558 | 1,154 |
| Steps 2 and 5, `2348 × 2050` | 2 + 298 + 257 = 557 | 1,149 |
| Step 4, `2348 × 4399` | 2 + 296 + 257 = 555 | 6,428 |

and the largest phase of a multiplication becomes the negation of the
scratch register, `sW + 2 = 4,400`:

| exponent register | base set | extra at peak | peak |
|---|---|---|---|
| 4096 qubits | 12,891 | 4,400 | **17,291** |
| 4095 qubits | 12,890 | 4,400 | **17,290** |

From an empty start the balanced circuit never exceeds 17,291 qubits.

## Conventions

The scratch of `Negate` and `AddScaled` is `shorGateResourceModel`'s
`cleanAnc`, counted as fresh qubits disjoint from everything live. The count
is of logical qubits of the circuit as lowered by the current allocator.
