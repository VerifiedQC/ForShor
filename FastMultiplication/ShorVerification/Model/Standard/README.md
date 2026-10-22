# `Model/Standard/`

A **consistency witness** for the semantic classes in `../Framework/`, and
nothing else.

Every headline theorem in the development is stated over a stack of typeclass
parameters — `qs : QSemantics`, `[RegEncoding qs.Basis]`, `[MeasureClass qs]`,
`[GateSemanticsFacts qs]`, `[LowerGateClass qs]`,
`[IdealCtrlModMulExactSemantics qs]`. Nothing outside this folder
instantiates any of them, and `#print axioms` cannot see that:
if one law were contradictory, every theorem would hold vacuously and the
axiom check would still report only `propext`, `Classical.choice` and
`Quot.sound`.

This folder builds one concrete model of all of those classes and checks that
the headline theorems specialise to it. It is a fourth sibling of
[`Framework/`](../../Framework), [`Implementation/`](../../Implementation) and
[`Submission/`](../../Submission). It is not a rule and not a circuit
construction: nothing here constrains what the rest of the development may do,
and nothing here is used to prove anything outside this folder.

Status: **the headline theorems specialise to this model**
(`Headline.lean`), and the specialisations depend on no axioms beyond
`propext`, `Classical.choice` and `Quot.sound`.

## The two import invariants

Both are one `grep` away, and both matter.

- **Outbound.** Every file here except `Headline.lean` imports only
  `../Framework/Quantum/`, `../Framework/Semantics/`,
  `../Framework/AbstractMachine/` and Mathlib. `Headline.lean` is the one file
  that reaches into `Implementation/` and `Submission/`, the way
  `Submission/Correct.lean` is one of the three `Submission/` files allowed
  to.
- **Inbound.** *Nothing outside this folder imports anything in it, ever.* The
  development's genericity in the model is the property being certified, and
  one stray import would silently lose it.

```
grep -rln "ShorVerification.Model" FastMultiplication FastMultiplication.lean \
  --include='*.lean' | grep -v "ShorVerification/Model/Standard/"
```

must print nothing.

The folder is also **additive**: it is not in the library root
`FastMultiplication.lean`, so `lake build FastMultiplication` does not see it.
Wiring it into the root build and the top-level docs is a deliberate, separate
decision.

## Building it

```
lake build FastMultiplication.ShorVerification.Model.Standard.Headline
```

Lake resolves any module under the `FastMultiplication.` prefix as part of the
default library without a root entry, and `Headline.lean` imports everything
else here, so this one command builds and checks the whole folder.

## The files

| file | provides | imports |
|---|---|---|
| `Basis.lean` | `ModelBasis := ℕ → Bool` and `instance : RegEncoding ModelBasis`, plus the register-locality lemmas everything downstream uses | `Framework/Quantum/Registers` |
| `Arith.lean` | the word-level `ℕ`/`ℤ` layer: two's-complement round trips, and `signedShiftLWord` / `signedShiftRWord` shown mutually inverse | `Framework/Semantics/GateSemantics` |
| `State.lean` | `State := ModelBasis →₀ ℂ` with the ℓ² inner product, `ket`, `qs : QSemantics`, `instance : MeasureClass qs` | `Basis`, `Framework/Quantum/` |
| `Lift.lean` | `permLift`, `diagLift`, `blockLift` and their ket equations | `State` |
| `BasisMaps.lean` | an `Equiv.Perm ModelBasis` for every `*_ket_total` law, and the model's `idealCtrlModMul` | `Basis`, `Arith` |
| `Blocks.lean` | the Hadamard and QFT matrices, their unitarity, and the diagonal phases | `Lift`, `BasisMaps` |
| `Gates.lean` | `evalG` and `instance : GateSemanticsFacts qs` | `Blocks` |
| `LowGates.lean` | `evalLG` and `instance : LowerGateClass qs` | `Gates` |
| `Headline.lean` | the headline theorems specialised to `qs` | everything, plus `Implementation/` and `Submission/` |

`Arith.lean` is an implementation split of `BasisMaps.lean`: the shift
arithmetic is the longest single piece in the folder and mentions no register,
no state and no `RegEncoding`.

## What the model is

- **The basis is `ℕ → Bool`.** `Reg` is any duplicate-free list of naturals,
  and `RegEncoding.toNat_writeNat_of_lt` must hold for *every* register. Take
  a register whose qubits exceed any proposed dimension and write a value with
  those bits set: read-after-write demands the value back. So no finite basis
  type can carry the class, and the fixed-`dim` vectors of a SQIR-style
  development cannot be the state type.
- **States are `ModelBasis →₀ ℂ`.** `QSemantics.state_induction` says every
  state is a *finite* linear combination of kets, so the state space is the
  algebraic span of the basis, not its completion. Kets are then literally the
  standard basis (`Finsupp.single b 1`), orthonormality is
  `Finsupp.single_apply`, every linear extension is
  `Finsupp.linearCombination`, and `state_induction` is `Finsupp.induction`.
  The ℓ² inner product is supplied through `InnerProductSpace.Core`.
- **Gates evaluate to `State ≃ₗᵢ[ℂ] State`.** `Gate.adj` is a free
  constructor, so the model *defines* its evaluation to be the inverse; then
  `eval_adj_apply`, `inner_preserved`, `eval_add` and `eval_smul` are all
  `LinearIsometryEquiv` API.
- **Three lifts, one construction.** Every primitive gate law gives the image
  of a ket explicitly, and the right-hand sides come in exactly three shapes:
  a relabelling of the basis (`permLift`), a diagonal phase (`diagLift`), and
  a `2^w × 2^w` block on one register (`blockLift`). Each is
  `Finsupp.linearCombination` of an orthonormal family with an explicit
  inverse of the same shape, so all three come from one lemma, `liftIso`.
- **`blockLift` is the SQIR-style part.** The matrices are the usual finite
  ones. What a fixed-dimension development writes as an explicit `kron` with
  the identity on every other qubit is here exactly the fact that
  `RegEncoding.writeNat r` touches only `r`'s bits.
- **Totality.** `eval` must be defined on *every* syntax term, including
  nonsense like `AddScaled` with overlapping registers. The laws already
  handle this: every basis map in `GateSemantics.lean` is total and reversible
  by construction (its guard returns `b`), and the one law stated under
  hypotheses, `eval_idealCtrlModMul_ket_exact`, leaves the model free outside
  them. The model takes the identity there; inside the guard it multiplies by
  a unit mod `N`, whose inverse is multiplication by `c⁻¹ mod N`.
