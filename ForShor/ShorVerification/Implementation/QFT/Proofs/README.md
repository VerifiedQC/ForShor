# `Proofs/`

Proof files. Other folders import `Hadamard.lean`, `QftPhase.lean` and
`Decomposition.lean` directly; everything else is reached through `Main.lean`.
See `Proofs/Lowering/README.md` for the plan/lowering correctness proofs.

## `Hadamard.lean`

`H_reg` on a register: one-qubit register and zero-split facts, the uniform
superposition `eval_Hreg_zero_uniform` with its normalization constants, and
`RegisterHadamardSemantics`: Hadamards on qubits of a register keep a state in
the finite span of basis states written into that register. Used by
`Proofs/Lowering/PlanSemantics.lean` and the modular-exponentiation proofs.

## `QftPhase.lean`

Facts about `qftPhase` and `ω`: its grid-exponential form and conjugate,
`ω r ^ r = 1`, periodicity in the first argument mod `r`, and unit norm. Used
by `ModularExponentiation/Proofs/CmpLtNW.lean` and
`Shor/Proofs/NaiveShor/OrderFindingAnalysis.lean`.

## `Macros.lean`, `MacroSemantics.lean`

The unsigned phase-product macros of `Statement.lean`. `Macros.lean` has
`PhaseProdWorkspace.Clean` and the register-value lemmas;
`MacroSemantics.lean` proves **`eval_PhaseProdUsing_ket`** /
**`eval_CPhaseProdUsing_ket`**: on a clean macro workspace,
`PhaseProdUsing`/`CPhaseProdUsing` contribute exactly the expected phase and
restore the basis state. The modular-exponentiation and Shor proofs use them
too.

## `Decomposition.lean`

Proves the high-level circuit identity that splits a QFT into two recursive
half-size QFTs, an unsigned phase-product macro, and a radix reversal —
independently of how any of those three pieces gets lowered to primitive
gates (that correctness is proved separately in `Proofs/Lowering/`).

- **`eval_QFT_split`** — the apex theorem, stated for a full `ExtReg` (active
  register plus reserve): on any state where the phase-product macro
  workspace is clean and the register has width ≥ 2,
  `Gate.QFT r` evaluates the same as running the QFT on the right half, then
  the unsigned phase-product macro, then the QFT on the left half, then a
  radix reversal — where the two recursive QFTs act on `r`'s active register
  split in half but keep sharing `r`'s reserve (`rightQFTReg`/`leftQFTReg`).
  This is the theorem `Proofs/Lowering/PlanSemantics.lean` calls at each split
  node to justify `QFTLoweringPlan`'s recursive case.
- **`eval_QFT_split_ofReg`** — the same identity for a bare `Reg` (no
  reserve bookkeeping) and an arbitrary state `ψ` (not just a basis ket);
  `eval_QFT_split` reduces to this plus the fact that `Gate.QFT` only depends
  on the active register, not the reserve.
- **`eval_QFT_split_ket_ofReg`** — the basis-ket case the above is built from
  by linearity: it derives the exact scalar phase (`qftPhase`) picked up by
  each amplitude, by chaining the two recursive QFT sums, the phase-product
  macro's contribution, and a re-indexing of the resulting double sum into
  the digit-reversed single sum that a radix reversal undoes.

The file also contains proof-local vocabulary not meant to be read as public
API: `finMulAddEquiv`, `nTot`, `leftQFTReg`, `rightQFTReg`, `j0`,
`j1` (register/index bookkeeping used only inside these proofs — deliberately
not deduplicated against similar-looking definitions elsewhere), and a small
`Fin`-casting utility section used to reindex the sums above.
