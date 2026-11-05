# Constructive thresholds: exact FPT algorithm; uniform P remains open

The profile-realization gap now has a constructive exact algorithm with running time

\[
  2^{O(k^4\log k)}\operatorname{poly}(\log(n+1)).
\]

Combined with the previously reviewed shared-table planner reduction, this gives exact recursive PP T-count optimization in

\[
  2^{O(K^4\log K)}\operatorname{poly}(n).
\]

These are parameterized bounds, with an exponential dependence on growing arity. **The requested uniform polynomial-time theorem is still unproved.** This report replaces neither that target nor its arbitrary-helper scope with a restricted constructor family. The full general search was defined and proved, but not implemented or run at large k.

## Retained model

The target remains KMY Appendix F.2's prescribed finite point family, using the repository's exact integer marker normalization, including negative reciprocal signs. Every row is writable; helper states and marker order are unrestricted; right shifts must be exact at every prefix; the complete table starts and ends at the identity. Charge is positive additions plus three times negative additions plus negations. The two history scanners determine the common-child-width profile. The recursive planner uses one fixed table for each arity, reused at every occurrence. K may grow. No monotonicity assumption on the arity sequence is introduced.

The outer bound is in numeric operand bitwidth n. It is not a claim of polynomial time in the binary encoding length log n. The new *local* threshold bound happens to have only polynomial dependence on log n, with its remaining work absorbed into the parameter factor.

For d in {0,...,k-1}, define

\[
\theta(k,d,C)=\min\{a\ge d:\text{a complete legal table has charge}\le C
\text{ and canonical profile}\le(a,a-d)\}.
\]

The value is infinity if no table exists. A truncated query must return the exact value and a table when theta<=n-2, or certify theta>n-2. Budgets 0<=C<=27k^3 suffice by the previously proved minimum-charge ceiling.

## What the new proof establishes

The full argument is in [the saturation and algorithm proof](algorithm_astra/SATURATION_AND_SINGLE_EXP_FPT.2026-10-15T190800.md), using [the symbolic cluster reduction](algorithm_astra/SYMBOLIC_THRESHOLD.2026-10-15T190000.md) and [the scanner normal-form bridge](normalform_astra/PRIMITIVE_NORMAL_FORM.2026-10-15T145600.md).

**1. Short, scanner-preserving witnesses.** Normalize every row by its common power of two after each charged operation. The replacement preserves each signed operation count, every exact marker, and identity restoration, while never increasing the peak for any nonnegative initial scanner vector. It has at most 3A+nu+2k-1 instructions, where A counts additions and nu counts negations. Thus minimum witnesses need O(k^3) instructions. The algebraic normal form existed in the September notes; preserving the present history scanner and asymmetric charge is the bridge proved here.

At a primitive boundary an addition is

\[
 Z=2^pY_i+\epsilon2^qY_j,\qquad \min(p,q)=0,
\]

followed by division by Z's maximal common power of two. If either p or q is positive, parity makes Z primitive already. Otherwise only the normalization exponent can vary. A fixed normalized addition template therefore has one exponent variable.

**2. Exact cancellation becomes finite linear alternatives.** For a fixed bounded operation template, every scalar row entry is a signed sum of power-of-two occurrences with affine exponent expressions. Retain multiplicity. Group sorted exponents into clusters, splitting at gaps at least H, where 2^H exceeds the number of occurrences. A lowest separated cluster cannot cancel a higher cluster unless it is itself zero. A coefficient-zero anchor at exponent zero similarly characterizes integrality. Applying this to every prefix enforces exact division legality, not just correct endpoints.

Once the order and small adjacent gaps are fixed, all exponent conditions are integer linear constraints. The exponentially long internal span is used only to accept or reject a pattern; it is not inserted as a large constraint constant. Unroll the scanner maxima into affine path upper bounds. This adds constraints but no integer variables. Exact prefix integrality and invertibility justify unclipped right subtraction.

**3. Every finite threshold occurs below an explicit k-only cutoff.** Let the accepted paired constructor have actual charge c0<=6k^2 and profile offsets a0,b0<=8k^2. If C>=c0, its padded cap gives theta<=a*=max(a0,b0+d)<9k^2. The optimizer remains free to choose a different table at a smaller cap.

Only C<c0 needs the general saturation argument. Here there are at most C+1<=m=6k^2 exponent-and-offset variables. All coefficients and right sides in an accepted uncapped linear pattern are bounded by B=8k^2. For the F.2 sequence, target coefficient exponents are O(k^2), not O(k log k).

The proof establishes the elementary small-integer-point lemma:

\[
 P=\{x\ge0:Ax\le b\},\quad |A_{ij}|,|b_i|\le B,
 \quad P\cap\mathbb Z^t\ne\varnothing
 \quad\Longrightarrow\quad
 \exists y\in P\cap\mathbb Z^t:\ y_i\le(t+1)t!B^t.
\]

Its proof bounds vertices and integer recession-ray generators by determinant minors, decomposes an integer feasible point into vertices plus rays, and subtracts the integer parts of the ray coefficients. The homogenized-cone argument covers lower-dimensional systems. The bound is independent of the number of inequalities.

Applying it to a true pattern of any feasible table yields

\[
 \theta(k,d,C)<\infty\ \Longrightarrow\ 
 \theta(k,d,C)\le S(k):=(6k^2+1)(6k^2)!(8k^2)^{6k^2}
 =2^{O(k^2\log k)}.
\]

The resulting point still represents a complete legal restored table. Primitive boundary constraints need not be imposed on every symbolic solution: legality is sufficient, and it can be normalized again before search.

## The constructive threshold algorithm

The symbolic systems prove the cutoff; the final algorithm need not enumerate those systems or call an integer-programming solver.

1. Compute the known constructor's c0,a0,b0. Return theta>n-2 immediately if n-2<d.
2. Set T=min(n-2,S(k)) when C<c0, and T=min(n-2,max(a0,b0+d)) otherwise.
3. Starting at the identity, enumerate all normalized macro words of charge at most C under cap (T,T-d). Each addition chooses distinct rows, its sign, and p,q with min(p,q)=0 and p,q<=T-1. Compute the forced normalization valuation exactly. Also allow negations.
4. Check both transient scanner peaks **before** normalization division. Record each required exact target at its first appearance; markers are free and their order is unrestricted.
5. Keep only words that cover every target and restore the identity. For each, compute its least ray cap max(d,a_word,b_word+d). Return the least such cap and its explicit marked instruction sequence. If there is no accepted word, return theta>n-2. Searching the full saturation cutoff without a witness also certifies global infeasibility.

There are O(k^2(T+1)) choices per charged step, at most C steps, and polynomial(T,k) exact arithmetic work per word. For C<c0, C=O(k^2) and log T=O(k^2 log k), giving 2^{O(k^4 log k)} time. For C>=c0, T=O(k^2) and C=O(k^3), giving the smaller 2^{O(k^3 log k)} bound. Reading and comparing n contributes polynomial(log(n+1)). Witness exponents have parameter-bounded bit lengths. Explicit replay also fits within the parameter factor because T is capped independently of n.

Four free prefix shifts transport a cap witness to any required exact canonical profile, as in the prior padding lemma. Therefore the algorithm supplies the reconstructing minimum-charge catalogues needed by the outer theorem.

## Consequence for recursive T-count

The [previous outer reduction](../gap_closure_2026-10-15/RESULT.2026-10-15.md) requires O(k^4) threshold queries per arity and polynomial(n,K) additional work. Substituting this constructive algorithm yields

\[
 2^{O(K^4\log K)}\operatorname{poly}(n)
\]

for the exact optimum and a consistent realizing table family. Repeated arities share the same selected profile and table. The earlier Kannan import belongs to that outer reduction; the improved local algorithm needs only finite normalized enumeration and the proved saturation bound.

## Review and verification

Parallel Astra lanes developed the construction, normalization, and refutations. A fresh Astra reviewer independently derived a carry/cancellation alternative to clustering and a homogenized-cone proof of the small-point bound. Reviews found no blocking defect in the stated parameterized results. These were independent reviews with proofs visible after preregistration, not blinded HG7 reviews.

The [first independent audit](independent_astra/INDEPENDENT_REVIEW.2026-10-15T150700.md) and [singly exponential review](refute_astra/SINGLY_EXPONENTIAL_REVIEW.2026-10-15T155500.md) record assumptions and limits. Author checks covered 579,195 exhaustive signed sums, 10,000 random sums, 44 structured cases, and 12,000 scanner checks. The separate carry implementation checked 121,135 cases; the refutation lane checked 20,000 additional exact dyadic sums. Normalization checks covered 57 full constructors and 500 seeded closed detours. A fixed complete k=2 skeleton was compiled to scanner/legality constraints and replayed in six relaxed-scanner ILP cases. These checks corroborate the local lemmas; they are not executions of the full general threshold enumeration.

The existing autoresearcher Lean workbench and autoformalizer trusted replay certified [five elementary integer implications](coordinator/FORMAL_CERTIFICATE.2026-10-15.md). The entire DSL, saturation theorem, runtime analysis, and recursive optimizer are **not** machine formalized. ResearchSkills S03/S04 and InventMath M03/M05 structured the proof and falsification work. MindPalace claims are staged through its schema, without changing the canonical graph. No local model inference was used.

A useful additional witness is [a complete k=3 table of charge 14 and profile (8,8)](refute_astra/K3_FULL_WITNESS.2026-10-15T151501.json), improving the previously available charge-14 profile (10,8). This is a constructive upper bound, with no global optimality claim. The [mandatory-departure lemma](refute_astra/MARKER_DEPARTURE.2026-10-15T150100.md) separately gives k=3 necessary bounds a>=4,b>=3. Larger tiny-cap searches that hit their stated cutoffs remain inconclusive.

## Exact remaining obligation

| Claim | Status after this round |
|---|---|
| Scanner-preserving primitive witness of O(k^3) length | Proved; independently reviewed |
| Finite theta bounded by S(k)=2^{O(k^2 log k)} | Proved; independently reviewed |
| Exact constructive threshold algorithm, 2^{O(k^4 log k)} poly(log n) | Proved; independently reviewed; full implementation not run |
| Shared-table recursive optimum, 2^{O(K^4 log K)} poly(n) | Consequence of the above and the previously reviewed outer theorem |
| Threshold realization in uniform polynomial(n,k) time | OPEN |
| Exact recursive optimization in uniform polynomial(n,K) time | OPEN at that remaining realization obligation |

The next theorem must replace exponential enumeration of complete charged operation words with a polynomial search or a polynomially searchable complete replacement family. Even polynomial saturation alone would leave that enumeration unresolved. Small-coefficient linear systems can force Fibonacci-sized variables, so coefficient bounds alone cannot supply polynomial saturation; this abstract observation is not an F2 counterexample, a hardness reduction, or evidence that the original problem is outside P.

Original inquiry files, ledgers, prior proofs, and canonical graph records were preserved. This is the new entry point for the threshold research round.
