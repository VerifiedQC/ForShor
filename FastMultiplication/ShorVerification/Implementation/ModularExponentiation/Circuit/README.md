# `Circuit/`

The concrete Algorithm-1 circuit: the static workspace structures it needs,
the Step-4 comparator it's built from, the five circuit steps and the
controlled modular-multiplication core they assemble, and the recursion over
the exponent register that turns one core into full modular exponentiation.
Internal order: `Workspace → CmpLtNW → Steps → ModExp` (each may import the
ones before it).

## `Workspace.lean`

- **`ModMulCoreLayout`** — the static register/qubit-disjointness layout every
  core invocation needs: `data`/`work` own disjoint qubits, and the flag/ctrl
  qubits are outside both and distinct from each other. `data.grow 1` appears
  because Algorithm 1 temporarily activates one reserve bit of `data` as its
  carry/high bit.
- **`ModMulCircuitWorkspaceOK`** — the static workspace condition for one
  controlled modular-multiplication core: `data` can grow by 2, `work` can
  grow by 1, and the two are disjoint. Its lemmas (`data_canGrow_one`,
  `dataCarry_canGrow_one`, `work_canGrow_one`, `dataCarry_work_disjoint`,
  `work_dataCarry_disjoint`) derive the smaller capacity/disjointness facts
  each individual step needs.
- **`ModMulCircuitWorkspaceOK.step1Workspace`** / **`.step2Workspace`** /
  **`.step5Workspace`** — carve the concrete `Gate.PhaseProdWorkspace` each of
  those three steps runs its phase product on, from the same two root
  registers.
- **`cmpLtNWWidth`** — the scratch-register width formula the Step-4
  comparator needs, as a function of the modulus and the data/work widths.
- **`CmpLtNWWorkspace`** — the static workspace condition for the Step-4
  comparator: a phase-product workspace between `work` and `scratch` with
  matching reserves, pairwise disjointness of `data`/`work`/`scratch`, the
  flag outside all three, and `scratch` sized to `cmpLtNWWidth`.
- **`ConstArithmeticWorkspace`** — the static physical conditions the concrete
  constant-arithmetic lowerers need (`data`/`scratch` can grow, are disjoint,
  the flag is outside both, and the constant `N` fits in the scratch width).
  Cleanliness is deliberately kept out of this record — it is a purely static
  precondition.

## `CmpLtNW.lean`

The concrete Step-4 comparator circuit.

- **`cmpLtNWSignQubit`** — the top bit of `scratch`, used as the sign bit
  after the difference is computed.
- **`fastConstMulInto`** — QFT `scratch`, apply the unsigned phase product
  scaled by `N`, then inverse-QFT: a fast constant multiplication into a
  clean scratch register.
- **`cmpLtNWDifference`** — the signed difference of the grown `data` register
  against `work`, computed via negation and scaled addition.
- **`cmpLtNW`** — assembles the three into the full comparator: multiply,
  difference, copy the sign bit to `flag`, then uncompute both in reverse.

## `Steps.lean`

The reusable high-level gates for Algorithm 1 and the five circuit steps they
assemble into `CmodMulInPlaceCore`.

- **`IQFT`**, **`H_reg`** — inverse QFT, and Hadamards across every qubit of a
  register.
- **`step1`** — prepare the work Fourier packet (Hadamards + inverse QFT)
  around a controlled phase-product load of the target residue.
- **`step2`** — a phase product transferring the work-label phase into the
  grown data-carry register.
- **`step3`** — `Gate.CmpGeConst`/`Gate.CSubConst`: compare the data-carry
  register against `N` and conditionally subtract it.
- **`step4`** — `cmpLtNW`, clearing the comparator flag set by Step 3 using
  the data-carry/work relation.
- **`step5`** — the adjoint cleanup for Step 1's fractional load, using the
  inverse constant `step5Constant`.
- **`step5Constant`** — the Step-5 cleanup constant `1 - c⁻¹ mod N`, chosen
  from the finite modular-inverse existence theorem.
- **`CmodMulInPlaceCore`** — the five-step controlled in-place
  modular-multiplication core: `step1 ;; step2 ;; step3 ;; step4 ;; step5`.
  This is the circuit `FinalModMul.lean`'s headline theorem is about, and
  the building block `ModExp.lean` recurses over.

## `ModExp.lean`

The ideal specification and the approximate recursion over the exponent
register, built from `CmodMulInPlaceCore`.

- **`tbits`** — the number of exponent/control bits used by modular
  exponentiation (the size of the exponent register).
- **`modExpIdealSteps`** / **`modExpIdeal'`** — the ideal modular-exponentiation
  recursion over a list of control qubits, applying `Gate.idealCtrlModMul` at
  successive powers `a^(2^e) mod N`; `modExpIdeal'` runs it over the whole
  exponent register.
- **`ModExpLayout`** — every exponent/control qubit has a valid
  `ModMulCoreLayout` against the shared `data`/`work` registers.
- **`ModExpArithmeticOK`** — every multiplier `a^(2^i) mod N` used by the
  recursion is coprime to `N`.
- **`modExpApproxStepsValid`** / **`modExpApproxValid`** — the approximate
  modular-exponentiation recursion over a list (resp. all) of control qubits,
  applying `CmodMulInPlaceCore` at each step under a fixed
  `ModMulCircuitWorkspaceOK`/`CmpLtNWWorkspace` pair. This is what
  `Spec/Assertions.lean`'s claim and `Proofs/ModExp.lean`'s theorem are about.
