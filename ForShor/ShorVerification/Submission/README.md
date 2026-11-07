# Submission

A submission is a Toom-Cook table: an arithmetic program over `k` limb registers, the interpolation points it evaluates at, and a proof that the pair satisfies four decidable side conditions (C1–C4). Everything else, the circuit, its correctness proof, the precision and the trial count, is fixed by this repository and is the same for every submission. A *policy* submission is a list of such tables indexed by operand width, so a wide table can be used at the top of the recursion and narrower ones below it.

This folder holds what a submitter writes, the check that accepts it, and the executable that prints what the resource estimator reads.

## The files

**`Template.lean`** is the file a submitter copies and edits. It holds `k`, the points, the table, and the four side-condition proofs. Each proof is a one-liner, because the conditions are decidable.

**`PolicyTemplate.lean`** is the same for a policy: the bands, each with its own table and proofs, the thresholds at which they take over, and the policy's negation method.

**`Decide.lean`** makes the four side conditions decidable, so `decide +kernel` closes them and Lean's kernel is what checks a submission, not a parser or the compiled evaluator.

**`Audit.lean`** defines `#assert_axioms`, a command that fails the build unless a declaration depends only on Lean's three standard axioms. It is what stops a submitter closing a side condition with `native_decide`, `sorry` or an axiom of their own.

**`Check.lean`** is the acceptance check: building it is the check. It runs `#assert_axioms` on the submitted table and states the certificate the table gets. Nothing in it is edited by a submitter. **`PolicyCheck.lean`** is the same for a policy, plus the check that the thresholds strictly decrease.

**`PolicyDecide.lean`** is an advisory check, not an admissibility condition: it reports whether each band's table actually recurses on the widths the band covers, so a submitter can spot a band that is dead weight.

**`Correct.lean`** is the certificate: the reference construction's correctness theorem, which is generic in the table, restated at the precision fixed for every submission. There is no per-submission proof to write; passing the side conditions is the whole acceptance test.

**`Score.lean`** fixes the two factors of the score once, for every submission: the declared success bound at that precision, and the trial count that amplifies it to 99% on 2048-bit moduli. The gate count itself is measured outside Lean, on the emitted IR.

**`Main.lean`** is the executable `forshor_submission`, which prints the submitted table, its IR, the precision and the trial count as one JSON document. It is a printer, not a checker: everything it reports was established by the build. **`PolicyMain.lean`** is `forshor_policy_submission`, the same for a policy; it also extracts the IR at run time and checks it against the real circuit before printing.

## The negation option

A policy may choose how a negation (`valid_ops.negate`, wherever the recursion reaches one) is built and priced, with one field next to its bands: `negation := .oneQubit` (the default, if the field is left out) or `negation := .scratch`. The two are a qubit against gate-count trade. `oneQubit` uses Gidney's single-ancilla increment: one clean qubit and about `12 w` Toffolis for a `w`-bit register. `scratch` adds against a clean register of ones as wide as the operand: `w + 1` clean qubits and `2 w - 3` Toffolis. The tables, the proofs C1–C4, the thresholds, the correctness certificate and the IR are the same either way, so the field is not an admissibility condition; what changes is the resource estimate. `forshor_policy_submission` prints the method as `negation`, the charge of one negation under it as `negate_charge`, and the charge under each method as `negate_charge_by_method`; `forshor_submission` prints `negation` (always `oneQubit`: a table submission has no such option) and its charge. A resource estimator must price the IR under the method the document names.

## Running it

```bash
lake build Submission && lake exe forshor_submission > ir.json
```

```bash
lake build PolicySubmission && lake exe forshor_policy_submission > policy.json
```

The `&&` matters: if the table is inadmissible the build fails and nothing is printed.
