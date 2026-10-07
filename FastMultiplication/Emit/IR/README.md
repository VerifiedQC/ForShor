# `IR/` — the extracted symbolic IR

Four files:

| file | what it is |
|---|---|
| `Syntax.lean` | the language: `WExpr`, `AExpr`, `RegExpr`, `Prop'`, `Node`, `Template`, `Doc` |
| `Instantiate.lean` | the only definition of what any of it *means* |
| `WellFormed.lean` | the structural checks a `Doc` must pass before anyone instantiates it |
| `Json.lean` | the printer, `forshor.ir/v1` |

Everything below is the semantics `Instantiate.lean` gives, stated once, naming the Lean definition it comes from.

Nothing here is a theorem. What is checked is that `instantiate` agrees with the real compiled circuit at the widths `Reflect/Verify.lean` samples — see
`../README.md`'s "What is and is not a theorem".

## Registers

Two types underneath everything (`Framework/Quantum/Registers.lean`):

- `Reg` — an **ordered list of distinct physical qubit indices**, not a
  range. `Reg.interval lo size` is `[lo, lo+1, …, lo+size-1]`, but a `Reg`
  reached by slicing need not be contiguous and its order is part of its
  identity. `regSize r` is the length.
- `ExtReg` — `{ active : Reg, reserve : Reg, disjoint }`. `width e` is
  `regSize e.active`; `capacity e` is `regSize e.reserve`.

A consumer that models registers as `(start, length)` pairs will diverge the
moment a slice is non-contiguous. Model them as lists.

## `WExpr` — width- and index-valued expressions

Evaluated by `IR.evalW` to a **natural number**. All arithmetic is `ℕ`
arithmetic, so `sub` is **truncated subtraction** (`5 - 7 = 0`) and `div` is
**floor division** (`7 / 2 = 3`). Both are load-bearing: `activeSlice`'s
`hi - lo` relies on truncation, and `qft`'s split point is `regSize r / 2`.

| constructor | meaning |
|---|---|
| `var name` | look `name` up in `Env.w`; unbound is an error, never `0` |
| `lit n` | the literal `n` |
| `add a b`, `mul a b` | `ℕ` addition, multiplication |
| `sub a b` | **truncated**: `a - b` in `ℕ`, i.e. `max 0 (a - b)` over `ℤ` |
| `div a b` | **floor**: `a / b` in `ℕ`; `b = 0` gives `0`, Lean's convention |
| `max a b`, `min a b` | `Nat.max`, `Nat.min` |
| `opaque fn args` | evaluate `args` left to right, then call `Env.opaqueW fn`; a `none` is an error (see **Opaque functions**) |

## `AExpr` — angle-valued expressions

Evaluated by `IR.evalA` to an `Angle`, which is a **rational number in units
of π** (`Framework/Quantum`). So `1/4` denotes `π/4`, and exact rational
arithmetic is required — floating point will not reproduce the circuits.

| constructor | meaning |
|---|---|
| `var name` | look `name` up in `Env.a`; unbound is an error |
| `lit a` | the literal angle |
| `mul a w` | `evalA a * (evalW w : ℚ)` — angle scaled by a width-valued weight |
| `coeff phi l m` | `evalA phi * c` where `c = Env.coeff l (evalW m)`; `none` is an error |
| `div2 a` | `evalA a / 2` |
| `neg a` | `-(evalA a)` |
| `signedPair phi xi xw zi zw` | `evalA phi * (signedBitWeight xw xi : ℚ) * (signedBitWeight zw zi : ℚ)` |
| `qftPhi m` | `2 / 2 ^ (evalW m)`, exactly — the QFT's per-level phase |
| `ratio num denom` | `(evalW num : ℚ) / (evalW denom : ℚ)`; `denom = 0` gives `0`, Lean's convention for `ℚ` |

`signedBitWeight w i` is `if i + 1 = w then -(2 ^ i) else 2 ^ i`
(`Implementation/PhaseProduct/Gates/NaiveLeaf.lean`): the two's-complement
weight of bit `i` in a `w`-bit register, so the **top** bit is negative. It
is a named construct rather than an expression because the sign depends on
the loop index relative to a symbolic width, and `WExpr` has neither signed
values nor exponentiation. `coeff` is the interpolation weight
`cramerCoeffFromPtsWidth k m pts hpts ⟨l, _⟩` and is opaque for the same
reason the width functions are: it depends on the table's points.

## `RegExpr` — register expressions

Evaluated by `IR.evalReg` to an `ExtReg`. Every result except `ext`'s has an
**empty reserve**: slicing produces `ExtReg.ofReg`.

| constructor | meaning |
|---|---|
| `var name` | look `name` up in `Env.r`; unbound is an error |
| `activeSlice r lo hi` | `ExtReg.ofReg (((evalReg r).active.drop lo).take (hi - lo))` |
| `reserveSlice r lo hi` | the same on `.reserve` |
| `ext active reserve` | `ExtReg.withReserve a.active b.active h` — **refused** with an error unless the two are disjoint; never assumed |
| `qubit r i` | the single-qubit register `Reg.singleton (r.active.get i)`; `i ≥ r.active.width` is an error |
| `grow r n` | `ExtReg.grow (evalReg r) n` (see below) |

`ExtReg.grow e n` appends the **first `n` qubits of `e.reserve`** to
`e.active` and keeps the rest as the new reserve:

```
grow e n = { active  := e.active ++ e.reserve.take n
             reserve := e.reserve.drop n }
```

`n > capacity` is not an error here — `take`/`drop` saturate — so the grown
register is simply shorter than asked. That is the real function's behaviour
and the IR does not add a check the circuit does not have.

Note what `grow` is *not*: the new active part is an append of two different
sources, so it is not a slice of anything nameable. That is why it is a
constructor rather than slice arithmetic.

## `Prop'` — guards

Evaluated by `IR.evalProp` to a `Bool`; `Node.cond` picks a branch with it.

| constructor | meaning |
|---|---|
| `lt a b`, `le a b`, `eq a b` | `ℕ` comparison of `evalW a` and `evalW b` |
| `testBit n i` | `Nat.testBit (evalW n) (evalW i)` — bit `i` of `n`, LSB first |

## `Node` — template bodies

Evaluated by `IR.evalNode` (to `LowGate`) or `IR.evalNodeGate` (to `Gate`).
The two differ only in the leaf dispatcher and the sequencing fold.

| constructor | meaning |
|---|---|
| `op name regs nats angle flags` | evaluate every argument, then build one gate — see **Ops** |
| `seq body` | evaluate each, then **right**-fold with `;;` and `id` for `[]` |
| `adj body` | `.adj` of the evaluated body |
| `cond guard t f` | `evalProp guard` picks `t` or `f`; the other branch is not evaluated |
| `call template wArgs aArgs rArgs` | evaluate the arguments **in the caller's env**, then run the callee's body in a **fresh** env binding only the callee's own parameters, with `opaqueW`/`coeff` carried over; costs one unit of fuel |
| `loop var lo hi body` | evaluate `body` once per `i` in `lo, lo+1, …, hi-1` with `var` bound to `i`, then right-fold as `seq` does; `hi ≤ lo` is the empty sequence |

Three things a consumer gets wrong by guessing:

- **`call` does not inherit the caller's variables.** A template body may
  reference only its own `wParams`/`aParams`/`rParams`. Leaking the caller's
  bindings hides missing arguments instead of erroring on them.
- **`fuel`** bounds `call` unrollings and nothing else. Running out is an
  ordinary error, not an invariant violation. Recursion terminates because
  each level's width strictly decreases (`WellFormed.lean`'s check 3), but
  the interpreter does not rely on that.
- **Folds are right-nested.** `[a, b, c]` is `a ;; (b ;; (c ;; id))`. If the
  consumer's sequencing is associative and drops identities this does not
  matter; if it compares trees, it does.

## Ops

`op` names are exactly the `LowGate`/`Gate` constructor names, with the
arguments split by kind: `regs` are register-valued, `nats` width/shift/index
values, `angle` the single `Angle` if the gate has one, `flags` the `Bool`s.
Each list is in the constructor's own declaration order.

Every **qubit**-shaped operand is a single-qubit `regs` entry built with
`RegExpr.qubit` — including ones that are a bare index in the Lean source
(`CCPhase`'s controls, `CSignedPhaseProd`'s `ctrl`, `CmpGeConst`'s `flag`,
`idealCtrlModMul`'s `ctrl`). A register whose active part is not exactly one
qubit where a qubit is expected is an error.

`buildLowGate` (`instantiate`):
`id`, `H`, `X`, `Phase`, `CPhase`, `CCPhase`, `CNOT`, `Toffoli`, `ShiftL`,
`ShiftR`, `Negate`, `AddScaled`, `zeroExtend`, `signExtend`, `zeroDealloc`,
`signDealloc`, `RadixReverse`.

`buildGate` (`instantiateGate`):
`id`, `H`, `X`, `CNOT`, `Toffoli`, `QFT`, `RadixReverse`, `SignedPhaseProd`,
`CSignedPhaseProd`, `CmpGeConst`, `CSubConst`, `ShiftL`, `ShiftR`, `Negate`,
`AddScaled`, `zeroExtend`, `signExtend`, `zeroDealloc`, `signDealloc`,
`idealCtrlModMul`. There is no `Gate` counterpart of `Phase`.

`CPhase` and `CCPhase` name `LowGate.CPhase`/`LowGate.CCPhase`, which are
**derived functions, not constructors**: they branch on whether the qubits
involved are equal (`ctrl = target`; for `CCPhase`, all three pairs). Those
branches are decided at instantiation, once the indices are concrete, and a
consumer must reproduce them — see `LowGate`'s own definition
(`Framework/AbstractMachine/LowGate.lean`). This is why they are not
expanded into `Node.cond`: the real function is not a symbolic guard either.

`RadixReverse` takes a bare `Reg`, so it uses the evaluated register's
`active` part.

## Opaque functions

`Doc.opaqueFns` lists every function the IR refers to by name and never
evaluates, with its arity. `Env.opaqueW` resolves the width-valued ones and
`Env.coeff` the interpolation weights. A miss is an error — the IR has no
default.

| name | arity | meaning |
|---|---|---|
| `nextWidth` | 2 | `RecursivePhaseWorkspace.nextWidth ops wx wz` — the common operand width after one level of the table's program |
| `reserveNeed_x` | 2 | `.1` of `RecursivePhaseWorkspace.reserveNeed ops wx wz` |
| `reserveNeed_z` | 2 | `.2` of the same |
| `qftXWork` | 1 | `.1` of `qftWorkspaceNeed ops w` |
| `qftZWork` | 1 | `.2` of the same |
| `log2` | 1 | `Nat.log2` |
| `mod` | 2 | `m % n` |
| `pow` | 2 | `b ^ e` |
| `modpow` | 3 | `(b ^ (2 ^ e)) % n` — note the **doubly** exponential exponent |
| `step5Const` | 2 | `step5Constant c N`: `(1 + N - cinv) % N` for the least `cinv < N` with `c * cinv ≡ 1 (mod N)`, and `0` if there is none |

The first five depend on the **table** (`ops`), which is why they are
tabulated rather than defined: a consumer cannot compute them without
reimplementing the compiler's width analysis. They are published in the
bundle's `width`, `split_width` and `qft_plan` sections, and
`Shor.tableOpaqueW` (`Symbolic/Width.lean`) is the oracle built from those
rows alone — `Emit/Tests.lean`'s `T4_1_TableOracle` section instantiates
`qft` at odd widths through it, which is the check that the published tables
really are sufficient.

Two subtleties about which rows exist:

- `width` holds only the **diagonal** `nextWidth w w`. That is enough for
  `phase_product`, whose recursion grows both children to `nextWidth` and so
  stays symmetric for ever after.
- `qft` splits a register of width `w` at `w / 2` and calls `phase_product`
  on `(w / 2, w - w / 2)` — **unequal at every odd `w`**. Those rows are
  `split_width`, one per `w`. Without them an odd-width QFT cannot be
  instantiated from the bundle at all.

The last five are ordinary arithmetic with no table dependence, and a
consumer implements them directly. `modpow` and `step5Const` are `shor`'s
alone.

## Templates in the shipped `Doc`

`phase_product` (the entry), `cphase_product`, `naive_leaf`, `naive_cleaf`,
`qft`, `shor_gate`, `shor`.

`pp_body` is **not** shipped, deliberately: it was R2.1's spike target and
its layout is built from fresh per-child reserve *variables* that nothing in
the document says how to bind. It remains extractable for the test suite
(`extract_ir_doc_with_pp_body`).

## Checking yourself against it

Instantiate a template with your own reader and diff against what this
repository's CLI prints for the same parameters. These six commands cover the
base and first recursive width of each shipped template, and an odd QFT width
where the split is unequal:

```bash
lake exe forshor_emit pp  2 8  1/4 --flat   # phase_product, base case
lake exe forshor_emit pp  2 12 1/4 --flat   # phase_product, first recursive width
lake exe forshor_emit cpp 2 8  1/4 --flat
lake exe forshor_emit cpp 2 12 1/4 --flat
lake exe forshor_emit qft 2 8      --flat
lake exe forshor_emit qft 2 9      --flat   # odd width: unequal split
```

The answer key is regenerated from the current code each time, so it cannot
go stale the way a committed one can.

## The registers, so a diff is possible at all

A circuit is only reproducible if the qubit *indices* are. `pp`/`cpp` lay
them out with `Shor.ppRegisters` and `qft` with `Shor.qftRegister`
(`Emit/Lower/Registers.lean`), both deterministic. Writing
`need = reserveNeed ops n n` and `slack = 1` (the CLI's value):

```
x.active  = [0 .. n-1]                  x.reserve = [n .. n+need.x+slack-1]
zStart    = n + need.x + slack
z.active  = [zStart .. zStart+n-1]      z.reserve = [zStart+n .. +need.z+slack-1]
ctrl      = zStart + n + need.z + slack  (cpp only, a single qubit)
```

and for `qft`, with `qneed = qftWorkspaceNeed ops w`:

```
r.active  = [0 .. w-1]                  r.reserve = [w .. w+qneed.x+qneed.z-1]
xWork     = r.reserve.take qneed.x      zWork     = (r.reserve.drop qneed.x).take qneed.z
```

The concrete values at the six widths above:

| command | `xw`/`w` | `xCap` | `z` starts at | `zCap` | `ctrl` |
|---|---|---|---|---|---|
| `pp`/`cpp` `n = 8` | 8 | 1 | 9 | 1 | 18 |
| `pp`/`cpp` `n = 12` | 12 | 11 | 23 | 11 | 46 |
| `qft w = 8` | 8 | 2 | — | — | — |
| `qft w = 9` | 9 | 2 | — | — | — |

For both QFT widths `xWork` and `zWork` are one qubit each: `[8]`/`[9]` at
`w = 8`, and `[9]`/`[10]` at `w = 9`.

## The environments

Exactly what `Reflect/Verify.lean`'s `phaseProductAgrees`,
`cPhaseProductAgrees` and `qftAgrees` build. `instantiate` is called with
fuel 200.

| template | `w` bindings | `a` | `r` |
|---|---|---|---|
| `phase_product` | `xw`, `zw`, `xCap`, `zCap` | `phi` | `x`, `z` |
| `cphase_product` | `xw`, `zw`, `xCap`, `zCap` | `phi` | `ctrl`, `x`, `z` |
| `qft` | `w`, `xWorkW`, `zWorkW` | — | `r`, `xWork`, `zWork` |

`opaqueW` and `coeff` come from the bundle: the width functions from the
`width`/`split_width`/`qft_plan` rows (see `Shor.tableOpaqueW`), the
interpolation weights from `coeff_poly` evaluated at the chunk width.

