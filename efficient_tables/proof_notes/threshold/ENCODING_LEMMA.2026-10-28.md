# The adjacent-gap encoding lemma and the saturation bound (closing repair item U1)

Status: written 2026-10-28; reviewed by two independent AI reviewers (proof review: CORRECT-WITH-FIXES, fixes applied; numeric test: no violation). These are not external refereeing and nothing here is machine-checked yet. See §8 and `review/`. Supplies the step that `proof_notes/threshold/SATURATION_AND_SINGLE_EXP_FPT…` §4 and `SATURATION_ADDENDUM…` §2 state without proof: that every constraint of the symbolic pattern systems has coefficients and right sides of size at most `8k^2`.

**Result.** No bound on `ν₂(A)` of a cluster integer is needed, and none is claimed. Integrality and cancellation are encoded by *adjacent* difference constraints, each with a constant at most `H + k^2`; the exponentially large relative spans of clusters are never written as a single constraint constant. Consequently `S(k) = (t+1)·t!·B^t` with `t ≤ C+1 ≤ 6k^2` and `B = 8k^2`, so `log S = O(k^2 log k)`, and the local bound `2^{O(k^4 log k)}` of the paper stands.

All inputs below are imported from the notes: the normalized instruction templates (`PRIMITIVE_NORMAL_FORM`, `SATURATION_AND_SINGLE_EXP_FPT` §3), the scanner constraints (`SYMBOLIC_THRESHOLD` §4), and the charge convention (positive addition 1, subtraction-type addition 3, negation 1).

## 0. Setting

Fix `k ≥ 2`, a charge budget `C < c0 ≤ 6k^2`, and a normalized skeleton `σ` with `A` additions, `A ≤ C` (each addition costs at least 1), and `N` negations. Its free integer variables are `x = (h_1,…,h_A, a) ∈ Z^{t}`, `t = A+1 ≤ C+1`, all `≥ 0`: one exponent variable `h_s` per addition (templates Q, P, R) and the cap `a`. Rows are `X_1,…,X_k`, initially the identity. Write `X^{τ}_{ij}` for entry `(i,j)` after step `τ`.

Put `M = 2^C + 1` and `H = C + 2`, so `2^H = 4·2^C > M`.

## 1. Occurrence structure

**Lemma 1.** For every step `τ` and entry `(i,j)`, the entry equals a finite sum `Σ_{o∈O} ε_o 2^{ℓ_o(x)}` (occurrences kept separate, including equal ones) with
1. `|O| ≤ 2^{α_τ}`, where `α_τ ≤ A` is the number of additions among the first `τ` steps;
2. `ℓ_o(x) = Σ_s η_{o,s} h_s` with every `η_{o,s} ∈ {-1,0,1}` (no constant term, no coefficient of absolute value above 1), and `η_{o,s} = 0` for every `s` whose instruction is not among the first `τ`.

*Proof.* Induction on `τ`. At `τ=0` each entry is `0` (empty `O`) or `1 = 2^0` (one occurrence, `ℓ = 0`). A negation of row `d` flips all `ε_o` of that row and changes nothing else. A left shift by `h_s` of row `d` adds `h_s` to every `ℓ_o` of row `d`, so `η_{o,s} = 1` for them; since `η_{o,s}` was `0` before (the instruction `s` was not yet executed), the claim holds. A right shift subtracts `h_s` likewise (coefficient `-1`). An addition `X_d ← X_d + ε 2^{h_s} X_{s'}` replaces each entry of row `d` by the union of the old `d`-entry occurrences and the `ε`-signed, `h_s`-shifted source occurrences; the source occurrences come from step `τ-1` and have `η_{·,s}=0`, so the shift gives `η = 1`. The count is at most `2^{α-1} + 2^{α-1} = 2^{α}` where `α` counts additions executed so far including this one, because each of the two parts comes from the state *before the current instruction*, in which at most `α-1` additions have been executed. Templates P and R compose a shift with an addition on the same variable `h_s` (one variable per addition): the shift and the addition are two consecutive steps, and only the addition increments `α`. The same argument applies step by step; the variable enters each occurrence at most once because it is attached to exactly one instruction. The template (Q, P or R) of each addition is part of the skeleton enumeration. Rows not touched are unchanged. ∎

Consequently every entry has at most `2^C` occurrences, and `ℓ_o` is a sum of at most `A` distinct variables with signs.

## 2. The scalar constraints

Two kinds of scalar constraint are imposed on entries, at every prefix:
* **(Z)** zero equations: `X^{τ}_{ij} − c = 0` at a marker/final identity entry, where `c` is the required target coefficient: `0` or a signed power `±2^{e}` with `0 ≤ e < k^2`. This adds one occurrence with constant exponent `e`.
* **(I)** integrality: `X^{τ}_{ij} ∈ Z` at every prefix. Add a distinguished **anchor**: one occurrence with coefficient `0` placed at constant exponent `0`.

In either case the expression has `m ≤ 2^C + 1 = M` terms, each with exponent `ℓ_o(x) + const` where `const ∈ {0, e}`.

## 3. Separation (zero and integrality criteria)

Let `S = Σ_{o=1}^{m} ε_o 2^{λ_o}`, `m ≤ M`, `ε_o ∈ {±1}` (an anchor has `ε=0`), `λ_o ∈ Z`. Sort by exponent; split between consecutive terms whenever the gap is `≥ H`; the pieces are **clusters**. Gaps inside a cluster lie in `{0,…,H-1}`. Define the **relative value** of a cluster as `Σ ε_o 2^{λ_o − λ_min}` (an integer fixed by the internal gaps alone).

**Lemma 2 (zero).** `S = 0` iff every cluster has relative value `0`.

*Proof.* (⇐) clear. (⇒) Let `G` be the lowest cluster, `A_G` its top exponent, `B` the minimum exponent of the next cluster, so `B − A_G ≥ H`. All terms outside `G` are integer multiples of `2^{B}` (exponents `≥ B`; `2^{λ−B} ∈ Z`, also if `B<0`). If `S = 0`, the value of `G` is an integer multiple of `2^{B}`; but `|G| ≤ m 2^{A_G} ≤ M 2^{A_G} < 2^{H}2^{A_G} ≤ 2^{B}`. So `G = 0`. Remove `G` and repeat. A single remaining cluster needs no argument. ∎

**Lemma 3 (integrality, with anchor).** Let `S` carry an anchor at exponent 0. Then `S ∈ Z` iff (i) every cluster strictly below the anchor's cluster has relative value `0`, and (ii) the anchor's cluster has an integer value.

*Proof.* The anchor's cluster has top exponent `≥ 0`, so every cluster above it has all exponents `≥ H > 0`: integral. (⇒ i) Let `G` be a cluster strictly below the anchor's cluster and `B` the minimum exponent of the next cluster in order; then `B ≤ top(anchor cluster)` and in fact `B ≤ 0` or the next cluster is the anchor's cluster whose minimum is `≤ 0`. In both cases `B ≤ 0`. If `S ∈ Z`, then `S` and every term above `G` are integer multiples of `2^{B}` (as `B ≤ 0`), so `G` is, and `|G| < 2^{B}` as in Lemma 2, so `G = 0`. Peel lower clusters in order. (⇒ ii) After removing the zero clusters below, `S` equals the anchor cluster plus clusters above, which are integers, so the anchor cluster is an integer. (⇐) The sum is the (integer) anchor cluster plus integral higher clusters. ∎

Both criteria depend on the data `(order, gaps)` only through the cluster structure and the relative values, which are determined by the gap labels, never by absolute exponents.

## 4. Patterns and the encoding lemma

A **pattern** `π` for a scalar constraint fixes a total order of its `m` terms and, for each adjacent pair, a label: an exact small gap `g ∈ {0,…,H-1}` or `LARGE`. It is **accepted** if the cluster test of Lemma 2 (resp. Lemma 3) passes on the relative values determined by the labels. Acceptance is a finite computation on integers of at most `M·H` bits, done once per pattern; it involves no variable.

The **system** `L(π)` of the pattern consists, for each adjacent pair `(u,v)` in the order, of the linear constraint on `x`

  `D_{uv}(x) := λ_v(x) − λ_u(x)  =  g`   if labeled `g`,   `D_{uv}(x) ≥ H`   if `LARGE`.

**Lemma E (encoding).** Let `π` be an accepted pattern for a scalar constraint of type (Z) or (I).
1. **Small constants.** Every row of `L(π)`, written `α·x ≤ β`, has `α ∈ {-2,…,2}^{t}` and `|β| ≤ H + k^2`.
2. **Soundness.** Every `x ∈ Z^t_{≥0}` satisfying `L(π)` satisfies the scalar constraint.
3. **Completeness.** If `x* ∈ Z^t_{≥0}` satisfies the scalar constraint, there is an accepted `π` with `L(π)(x*)` true.

*Proof.* 1. `λ_o(x) = ℓ_o(x) + const_o` with `ℓ_o` a ±1,0 combination (Lemma 1) and `const_o ∈ {0, e}`, `0 ≤ e < k^2`. So `D_{uv}` has variable coefficients in `{-2,…,2}` and constant part `const_v − const_u ∈ (−k^2, k^2)`. The right side is `g − (const_v − const_u)` with `0 ≤ g ≤ H-1`, or `H − (const_v − const_u)`. Hence `|β| < H + k^2`. (Equalities are two inequalities.)
2. Let `x` satisfy `L(π)`. Then the exponents `λ_o(x)` are in the order of `π`, with exactly the gap labels of `π`, so the clusters of `S(x)` are those of `π` and their relative values are those computed in the acceptance test. Acceptance and Lemma 2 or 3 give the constraint.
3. Order the terms by `λ_o(x*)` (ties arbitrarily), label each adjacent gap with its value if `< H` and `LARGE` otherwise. The pattern is satisfied by `x*` by construction, and it is accepted by Lemma 2 or 3 applied to `x*`. ∎

The proof never mentions `ν₂` in any constraint. The cluster integers `A` (relative values) and their valuations occur only inside the acceptance test of a fixed pattern, which is a finite computation independent of `x`. (For the anchor cluster, the exact-gap chain from the anchor, which sits at constant exponent 0, fixes the absolute position of the cluster, so the integrality test is a finite check that also pins `λ_min`.)

## 5. The pattern polyhedron and saturation

For a skeleton `σ`, a choice `Π` of one accepted pattern for every scalar constraint of `σ` (all prefixes, all markers, final identity), together with the scanner constraints, defines
  `P_{σ,Π} = { x ∈ R^t : x ≥ 0, α·x ≤ β }`.

**Scanner rows.** For every instruction boundary (including the post-add, pre-right-shift peak of template R and the post-left-shift peak of template P, which are two consecutive steps), every row index `i`, and both `r ∈ {0, k−1}`, impose that each unrolled max-plus path value is `≤ a` (for `r = 0`) or `≤ a − d + k − 1` (for `r = k−1`). A path value is an affine form with exponent coefficients in `{-1,0,1}` (each instruction occurs at most once on a path) and constant at most `(number of additions and negations on the path) + (k−1 if r = k−1) ≤ C + k − 1`. Moving `a` to the left side, each row has coefficients in `{-2,…,2}` and `|β| ≤ C + d + k − 1 ≤ 6k^2 + 2k` (a looser bound `C + 2k + d ≤ 6k^2 + 3k` also suffices). For soundness, the unrolled affine path value equals the true width for every `x` satisfying the pattern system, because the integrality constraints (I) and invertibility of the prefixes exclude any clipping of a right shift (`SYMBOLIC_THRESHOLD` §4, "no max branch is guessed"). This is imported from that note, not reproved here.

**Bounds on the variables.** The templates carry `h_s ≥ 1` (Q, P) or `h_s ≥ 0` (R), `x ≥ 0`, and `a ≥ d`; each has right side of absolute value at most `k − 1`. The target exponents `e < k^2` are imported from `SATURATION_AND_SINGLE_EXP_FPT` §4 (the first `2k−1` points of the F2 family have dyadic exponent at most `k`, so every nonzero target coefficient is `±2^{e}` with `e ≤ k(k−1)`); I did not recheck the F2 point set itself.

**Lemma 4 (B ≤ 8k²).** With `C ≤ 6k^2 − 1`, every row of `P_{σ,Π}` has `|α_i| ≤ 2` and `|β| ≤ 8k^2`.

*Proof.* Pattern rows: `|β| < H + k^2 ≤ (C+2) + k^2 ≤ 7k^2 + 1 ≤ 8k^2` (as `C ≤ 6k^2 − 1`; `7k^2 + 1 ≤ 8k^2` iff `k^2 ≥ 1`). Scanner rows: `6k^2 + 3k ≤ 8k^2` iff `3k ≤ 2k^2` iff `k ≥ 3/2`. The variable bounds (`h_s ≥ 1` or `≥ 0`, `x ≥ 0`, `a ≥ d`) have constants `≤ k − 1`. ∎

**Theorem (saturation).** Let `θ(k,d,C)` be finite with `C < c0`. Then `θ(k,d,C) ≤ S(k) := (t+1)·t!·B^t` with `t = C+1 ≤ 6k^2`, `B = 8k^2`; so `S(k) ≤ (6k^2+1)(6k^2)!(8k^2)^{6k^2} = 2^{O(k^2 log k)}`.

*Proof.* A witnessing complete table, normalized, gives `σ` and an integer point `x*` satisfying all scalar constraints and scanner constraints with `a = θ`. By Lemma E.3 choose `Π`; then `x* ∈ P_{σ,Π}`. By Lemma 4 and the small-integer-point lemma (`proof_notes/threshold/SATURATION_AND_SINGLE_EXP_FPT…` §5, formalization WP-4c), `P_{σ,Π}` has an integer point `y` with every coordinate, in particular `y_a`, at most `S(k)`. By Lemma E.2 and the soundness of the scanner rows (`SYMBOLIC_THRESHOLD` §4), `y` is a complete legal table of charge `≤ C`, with cap `y_a`. So `θ ≤ y_a ≤ S(k)`. ∎

## 6. What is and is not claimed

* Claimed: Lemma 1, Lemma E, Lemma 4 and the saturation theorem, given the imported normalized templates, scanner constraints and the small-integer-point lemma.
* **Not claimed:** that `ν₂(A)` is small for every realizable cluster (it can be as large as the number of terms for a cluster like `1+1+2+4+…`), nor any polynomial saturation: the Fibonacci system in `SATURATION_CLARIFICATIONS` shows that coordinates of a forced solution can be exponential in `t`, consistent with `S(k) = 2^{O(k^2 log k)}`.
* Difference from the report (A): A encodes integrality of a group as an inequality `µ + ν₂(|A|) ≥ 0`, whose constant `ν₂(|A|)` can be exponential (`< MG`), hence its `O(k^2)`-bit `B`. The anchor encoding here avoids that constant. The two encodings give different local costs (`2^{O(k^4 log k)}` by enumeration here, `2^{O(k^4)}` by the sign-case route there) and are both valid; neither is a mistake.
* Variable count: this note uses one variable per addition (`t ≤ C+1`). The single-exponential review writes `t ≤ 2C+1`; with `t ≤ 12k^2` the bound is still `2^{O(k^2 log k)}`, so the conclusion does not depend on which is right.

## 7. Open points for the reviewers
(a) Lemma 1(2): is it true for the templates P and R that the single variable `h_s` enters an occurrence at most once, even when the same row is both source and destination across steps? (b) Lemma 3: the position of the anchor relative to cluster boundaries. (c) Lemma E.2: does `L(π)` pin the order and cluster structure for *all* terms, including those joined only through chains? (d) Are there any other constraint types in the symbolic system (beyond (Z), (I), scanner rows, `x ≥ 0`, `a ≥ d`) whose constants are not bounded as in Lemma 4? (e) Sizes: occurrence bound `2^C + 1` including the target/anchor term.

## 8. Verification record (2026-10-28)
* **Proof review** (`review/review_proof.md`): CORRECT-WITH-FIXES. Lemmas 1–3, E and 4 re-derived independently; four minor underspecifications (scanner rows, variable bounds, a citation, wording) fixed in this version. `t ≤ C+1` confirmed; the `t ≤ 2C+1` of the earlier single-exponential review comes from a superseded case split and is harmless.
* **Numeric test** (`review/review_numeric.md`): no violation. Covered: Lemma 1 on 593,992 prefix entries (k = 2–4, up to 9 additions; the `2^α` bound is attained); Lemmas 2–3 on 203,195 sums including exactly `2^C+1` terms and gaps `H−1`/`H`; Lemma E on 658,840 shifted points including offsets near `10^12`; Lemma 4 bounds hold (largest observed pattern row `|β| = 39`, scanner `18`). Cluster `ν₂` up to 7 observed without any large constant appearing.
* **Not covered:** `k ≥ 5`; charge near `6k^2`; the imported lemmas (normalized templates, scanner no-clipping, the F2 target exponents, the small-integer-point lemma). The small-integer-point lemma is being formalized separately (`proof_notes/formal/`).
* Still imported unproved here: the primitive normal form and scanner transfer (`PRIMITIVE_NORMAL_FORM`, `SYMBOLIC_THRESHOLD` §4).
