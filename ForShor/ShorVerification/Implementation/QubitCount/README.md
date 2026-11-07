# QubitCount

This folder works out how many qubits the lowered order-finding circuit needs at once, and proves an exact formula for it. There is a version for the plain circuit and one for the circuit after the balanced split in `Reference/Balanced/`.

## What gets counted

We walk the lowered circuit in order and keep track of which qubits are live. A gate makes the qubits it touches live. Extending a register brings reserve qubits in, and deallocating releases them. The peak is the largest the live set ever gets.

`AddScaled` and `Negate` also borrow clean scratch qubits while they run. `AddScaled` borrows one carry. What `Negate` borrows depends on the negation method the policy asks for (`P.negation`, a `NegationMethod`):

- `oneQubit` (the default): negation is the complement followed by a one-clean-ancilla increment gate, so it borrows one qubit.
- `scratch`: negation is the complement followed by an addition against a constant-one register as wide as the register it negates, plus the adder's carry, so it borrows the register's width plus one. This is the model that held before modular swap 001, and it reproduces the numbers of that time.

Those qubits are added in while the primitive runs and returned afterwards. Every budget and every theorem below is stated for both methods: `scratchFor m` is the scratch charge of the method `m`, the budgets take `m` (written `P.negation` at the level of a policy), and a policy submitted with `negation := .scratch` is counted with the register-wide charge while one that names no method is counted with the one-qubit charge.

This is not the same as the number of qubits the circuit ever touches (`LowGate.qubitCount`). The allocator gives every child of a phase-product recursion its own reserve, but the children run one after another, so only one of them is live at a time.

## Files

- `Statement.lean` has the counting walk, the closed-form budgets and the claims. It doesn't import anything else from this folder.
- `Proofs/` has the lemmas: one file per piece of the circuit (a recursion level, a phase product, the QFT, a modular multiplication, the whole order-finding circuit), plus the 2048-bit numerals. `Proofs/PolicyPeak.lean` is the interface for costing an arbitrary policy at the 2048-bit reference widths: it reduces the peak of the reference circuit to `Policy.orderFindingPeak P` (or `Policy.orderFindingPeakBalanced P`), which the kernel can evaluate on a concrete policy.
- `Main.lean` proves the three formulas:
  - `Policy.orderFinding_peak_formula`: the peak is the base registers plus the most expensive step, for any admissible policy, counted with that policy's negation method.
  - `Policy.orderFinding_peak_formula_balanced`: the same for the balanced circuit, where each site costs its split if the spare qubits hold it and the plain product otherwise.
  - `Policy.orderFinding_peak_formula_balanced_u`: the same for the unconditionally balanced circuit, where every site is split and the count depends on the register widths alone.

## The 2048-bit numbers

These are for the reference circuit with the standard `k = 2` table. The registers are data 2048, work 2347 and scratch 4398 qubits, and the exponent register is 4095 or 4096 qubits depending on `N`. With a 4096-qubit exponent register:

| circuit | method | base registers | most expensive step | peak |
|---|---|---|---|---|
| plain | `oneQubit` (default) | 12,891 | Step 4's phase product, 6,428 | **19,319** |
| plain | `scratch` | 12,891 | Step 4's phase product, 6,428 | **19,319** |
| balanced | `oneQubit` (default) | 12,891 | Step 1's phase product, 558 | **13,449** |
| balanced | `scratch` | 12,891 | negating the scratch register, 4,400 | **17,291** |

With 4095 exponent qubits, take one off each. The plain circuit peaks in Step 4 because that phase product multiplies a 2348-bit register by a 4399-bit one, and this is the same for both methods. Balancing splits it into two 2348 × 2348 products, which cost 553 qubits instead. What is then the largest step depends on the method. With `scratch`, Step 3's constant arithmetic on the 4398-qubit scratch register needs its unit qubit plus the register-wide constant and carry, 4,400 qubits, so that is the largest step. With `oneQubit` it needs 3, and Step 1's phase product, plus the 2 extra qubits every phase-product step adds (the `2 +` in `modMulPhasePeaksWith`), is the largest (558).

The numbers are proved in `Proofs/Numerals.lean` and `Proofs/BalancedNumerals.lean`, checked by the kernel (`decide +kernel`). Each theorem has a form for a general method `m` (`..._for`) and the two instances: the unsuffixed name is the default `oneQubit` method, and `_scratch` is the `scratch` method (`standardPolicy2S`). The formula without scratch was also compared against the real compiled circuit from `forshor_emit` for small instances, and it matched every time.

## Peaks of the STO-table policies (kernel-evaluated)

`Proofs/PolicyNumerals.lean` (the `scan` rule, in the `ForShor` build) and `Proofs/PolicyNumeralsExact.lean` (the `exact` rule, a library of its own that CI builds in a separate step), with `Proofs/PolicyNumerals/`, cost the six phase-product policies of `Submission/Policies/` that the sister repositories' `policies/*.json` define (`ref_pp_2048`, `k5_sixband_2048`, `threshold_declared_pp`, `threshold_degenerate_pp`, `threshold_noshrink_pp`, `threshold_scanonly_pp`) at the 2048-bit reference widths. Every theorem is stated for both negation methods and, where available, both width rules: `scan` (the field every submission has unless it asks otherwise) and `exact` (the benchmark mode of the sister repositories' `JMC_VALIDATION.md`). Of the six, `ref_pp_2048` and `k5_sixband_2048` are accepted by the sister repositories' acceptance rule, `threshold_scanonly_pp` only under `exact`, and `threshold_declared_pp`, `threshold_degenerate_pp` and `threshold_noshrink_pp` are rejected (see `Submission/Policies/`): ForShor admits all of them (the recursion falls back to the leaf), so the table costs them as circuits and does not certify them. The two `faulty_*` policies are negative controls and have no peak, and the `*_ptp` policies have no order-finding budget in this repository.

Each peak is a statement about the reference circuit, not just about the closed form: for every 2048-bit modulus and exponent width `xW` (4095 or 4096), the reference circuit lowered by the policy peaks at `xW + 8795 + N` qubits, where `8795` is the data register with its carry bit, the work register, the scratch register and the flag, and `N` is a numeral closed by `decide +kernel`. The claims are `ReferencePeakIs`, `ReferenceBalancedPeakIs` and `ReferenceBalancedUPeakIs` (`PolicyNumerals/Basic.lean`), and the theorems are named `plain_<rule>_<method>`, `balanced_<rule>_<method>` and `balancedU_<rule>_<method>` in `PolicyNumerals.<Policy>` (scan) and `PolicyNumerals.<Policy>Exact` (exact).

The balanced theorems have no hypothesis about the allocator's spare capacities. The reference layout is sized so that the default rule's split fits at every site (`Balanced.reference_fits`), and where every split fits the balanced count equals the width-only count of the every-site-split circuit (`orderFindingQubitsBalanced_eq_U`); `reference2048PeakBalanced_policyU` combines the two, so `N` is `Policy.orderFindingPeakU` and no capacity is evaluated. (The balanced and the every-site-split reference circuits are the same circuit at the reference layout, `balancedUShorCircuit_eq`.)

The qubit counts below do not depend on the exponent width except through the `xW` term; they are for `xW = 4096` (take one off for 4095). They contain no T count.

The total is `4096 + 8795 + N = 12,891 + N`. The plain total is the same under both methods.

| policy | width rule | plain: N, total | balanced, `oneQubit`: N, total | balanced, `scratch`: N, total |
|---|---|---|---|---|
| `ref_pp_2048` | exact | 23,182, **36,073** | 606, **13,497** | 4,400, **17,291** |
| `ref_pp_2048` | scan | 23,724, **36,615** | 936, **13,827** | 4,400, **17,291** |
| `k5_sixband_2048` | exact | 18,854, **31,745** | 554, **13,445** | 4,400, **17,291** |
| `k5_sixband_2048` | scan | 19,250, **32,141** | 782, **13,673** | 4,400, **17,291** |
| `threshold_declared_pp` | exact | 23,176, **36,067** | 602, **13,493** | 4,400, **17,291** |
| `threshold_declared_pp` | scan | 23,678, **36,569** | 892, **13,783** | 4,400, **17,291** |
| `threshold_degenerate_pp` | scan | 23,788, **36,679** | 1,002, **13,893** | 4,400, **17,291** |
| `threshold_noshrink_pp` | exact | 23,218, **36,109** | 650, **13,541** | 4,400, **17,291** |
| `threshold_noshrink_pp` | scan | 23,788, **36,679** | 1,002, **13,893** | 4,400, **17,291** |
| `threshold_scanonly_pp` | exact | 23,218, **36,109** | 650, **13,541** | 4,400, **17,291** |
| `threshold_scanonly_pp` | scan | 23,788, **36,679** | 1,002, **13,893** | 4,400, **17,291** |

What the table shows (a reading of the numbers above, not separate theorems):

- The plain peak does not depend on the negation method (the largest step is a phase product that negates nothing wide), exactly as for the standard `k = 2` table.
- Balancing brings the `oneQubit` peaks down to the phase products' own costs (a few hundred to about a thousand qubits above the base registers). Under `scratch` every policy's balanced peak is 17,291: Step 3's constant arithmetic on the 4398-qubit scratch register costs 4,400 and is larger than every phase product, the same number as for the standard `k = 2` table.
- For the plain peak and the `oneQubit` balanced peak, the `exact` width rule gives smaller values than `scan` for every policy that has an `exact` row (the `scratch` balanced peak is 4,400 under both rules). `threshold_degenerate_pp` has none: the kernel's evaluation of its exact width (the `k = 6` table applied at widths `1 ... 4`) takes over five minutes, so only its `scan` numerals are stated (the interpreter's `exact` values are not kernel-checked and are left out).

Every numeral in the table is also checked by the compiled interpreter (`#guard` in each file), independently of the kernel; and, reading the table, the `scratch` peaks are at least the `oneQubit` peaks everywhere.

Cost, measured with `/usr/bin/time -l` on one module at a time (`lake env lean`): importing the library alone is 3.8 GB and 6 s. The six `scan` modules take 10 to 13 s and peak at 4.5 GB (`ref_pp_2048`, `k5_sixband_2048`), 4.9 GB (`threshold_declared_pp`, `threshold_noshrink_pp`, `threshold_scanonly_pp`) and 5.4 GB (`threshold_degenerate_pp`). The five `exact` modules take 33 to 40 s and peak at 9.4 to 11.9 GB, which is why they are a separate library, chained by import so that only one builds at a time, and built by a CI step of their own after the main build.
