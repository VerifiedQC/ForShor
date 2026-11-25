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

### Order-finding readout

```bash
lake exe forshor_policy_submission --balanced --readout coherent
lake exe forshor_policy_submission --balanced --readout semiclassical
```

Coherent is the default. In the local opt-in verifier, leave the `policy` record unchanged
and add this public definition inside `namespace PolicySubmission` in the same file:

```lean
def submittedDesign : Shor.SubmissionDesign where
  readout := .semiclassical
```

Omit `submittedDesign` or use `readout := .coherent` to keep coherent readout. The
verifier checks the declaration's type and axiom dependencies before extracting IR.
This does not enable the option in hosted intake. `--readout coherent` and `--readout semiclassical`
are local preview overrides. A trusted verifier uses `--balanced --readout submitted`:
there is no override in that mode, and its output records the compiled `submitted_readout`.
Neither choice changes the arithmetic policy, declared single-run success bound or trial
count. The semiclassical document (`forshor.policy-submission-semiclassical/v1`)
contains a fixed measurement schedule (`forshor.readout-loop/v1`) and one balanced controlled
multiplication template, `ir.entry = readout_round`. Run `initY1` and then the listed steps for
`j = 0, …, referenceXWidth inst - 1` with `rounds = referenceXWidth inst`, the same
`referenceControl` in every round, and the reference arithmetic registers. Only the sample
agreement checks unroll the rounds. Use a consumer that explicitly supports this schema;
the legacy coherent IR pricer is not a measured-readout pricer.
The guarded balanced arithmetic uses the existing templates. On the reference layout its
circuit equals the every-site-split version (`balancedUSemiclassicalProgramAt_circuit_eq`,
`Balanced.referenceFits_default`), which is the version used by the width-only peak formula.

### Synthesis opt-ins

Two more optional, public declarations go inside `namespace PolicySubmission` in the same file, read
by exact name like `submittedDesign` (absent chooses the default; a `private` one, one of another
type, or one that depends on an axiom outside the allowlist is an error):

```lean
def submittedPrimitive : Shor.PrimitiveSynthesis := .catalyticB2   -- or .adaptiveB3; default .rossSelinger
def submittedFullRunDesign : Shor.FullRunDesign := Shor.FullRunDesign.quotientCatalytic   -- default .reference
```

What `lake build PolicySubmission` refuses, as kernel-checked theorems in `PolicyCheck.lean`:
a full-run design that is neither one of the eight qualified profiles (`FullRunDesign.qualified`) nor a
QFT-backend-only design on the reference topology; a full-run design together with a non-default
primitive; a full-run design with a coherent saved readout, each with a message naming the rule. The `exponent` family is not accepted, since
a full run is priced on the semiclassical readout, which has no exponent register. A ceiling is compared
as a number and printed in lowest terms: `250e-6` is `25e-5`. What the executable refuses, because it depends on flags: a full-run
design needs `--balanced --readout submitted`; a non-default primitive needs `--balanced` or `--exact-widths`;
neither works with `--width-table`.

Each optional declaration is read as its kernel value, not by name, so a compiled-code attribute cannot make
the printed selection differ from the one the build-time rules judged.

The output then carries `submitted_full_run` (`profile`, or `design` for a body, never both) and
`submitted_primitive`. These are **declarations**, not Lean-certified claims: this repository attests
the typed choice, and the circuit and its price are checked by the consumer (the results engine), which
refuses any combination it cannot price. PhaseTripleProduct policies take `submittedPrimitive` only;
`PTPPolicyCheck.lean` refuses `submittedFullRunDesign` at build time.

## PhaseTripleProduct policy submissions

A PhaseTripleProduct policy (a width-indexed list of `Shor.PTP.PTPTable`s, `2 ≤ k ≤ 8` per band) is submitted the same way as
a PhaseProduct policy, with its own three files:

| File | Owner | What |
|---|---|---|
| `PTPPolicyTemplate.lean` | the submitter | the tables (`k`, `3 k - 2` points, the program), their point counts (`by decide`) and `PTPPolicySubmission.policy : PTP.PTPPolicy` |
| `PTPPolicyCheck.lean` | this repository | `lean_lib PTPPolicySubmission` is rooted here: `PTPPolicy.check` (thresholds strictly decrease, every table passes the contract) and `chainContractsTight 2048` (the exact-width threshold rule) by `decide +kernel`, an axiom audit, and `correct_exact`, `thresholds_at_target`, `peak_exact` stated at the policy |
| `PTPPolicyMain.lean` | this repository | `lean_exe forshor_ptp_policy_submission` prints the bands (`threshold`, `k`, `points`, `ops`, in the PhaseProduct document's spelling), the negation method and the benchmark width |

```bash
bash scripts/check_template_lexical.sh ForShor/ShorVerification/Submission/PTPPolicyTemplate.lean   # the lexical gate, step 1
lake build PTPPolicySubmission forshor_ptp_policy_submission && lake exe forshor_ptp_policy_submission > policy.json
```

The lexical gate is the one the PhaseProduct template uses, unchanged. It reads the file as tokens, with comments
blanked, and refuses a forbidden attribute or command wherever it sits (stacked after another attribute, after
`open … in`, in a multi-line attribute list, on a line with `namespace`), not only at the start of a line;
`scripts/test_check_template_lexical.sh` pins both what it refuses and what it lets through. It refuses compiled-code attributes
(`implemented_by`, `extern`, `csimp`) and the metaprogramming surface, which a PTP table could otherwise use to be
kernel-checked as one thing and printed as another. Nothing in a `PTPTable` or a `PTPPolicy` is a proof, so
the build's kernel checks and `#assert_axioms` are the whole of the acceptance.

What differs from the PhaseProduct submission: there is no IR, no `--balanced` and no agreement tier, since a
PhaseTripleProduct policy has no ForShor emitter; the boards count its T and qubits in the results engine
(Python, Qualtran) at exact widths. The executable does not evaluate the exact-width ladder at run time: the
compiled evaluation of that recursion takes many minutes at a `k = 8` band, and the kernel proves the same
rule in seconds at build time. Measured: a policy with bands `k = 8` and `k = 4` builds and passes in about
25 seconds; a one-band `k = 4` policy (the shipped template) in under 20.
