# Symbolic exponent clusters: constructive k-only FPT threshold route

Status: mathematical derivation and independent finite checks; parent and adversarial review pending. The uniform polynomial-time threshold theorem remains OPEN. The new algorithm below has a doubly exponential parameter factor, so it must not be described as a P result.

The parent proposed the symbolic-exponent route. This lane independently checked the cancellation/integrality reduction, supplied the linear scanner-upper-bound formulation, and derived the bounded witness recovery and parameter estimates. No local model inference was used.

## 1. Precise target and imports

For k>=2, 0<=d<k, 0<=C<=27k^3, theta(k,d,C) is the least a>=d admitting a complete restored F2 PP table of charge<=C and canonical profile <=(a,a-d). Given n, return the exact theta and a realizing instruction sequence if theta<=n-2, or a correct report theta>n-2.

All k rows remain writable, helpers and marker order unrestricted, integer right shifts exact, start/end I, and add/negative-add/negation prices are1/3/1. The F2 target is the actual repository integer row. In particular negative reciprocal signs are not changed to positive-denominator manuscript normalization. No restriction on recursive arity order or table reuse is introduced.

Imports and applicability:

* Accepted gap-closure polynomial-witness and charge-staircase results apply to this exact scanner and target contract. They give a minimum-charge witness of at most L(k)=(k+1)(27k^3+2k-1)+k+4=O(k^4) instructions for every feasible cap. If any charge<=C table exists, its cap-minimum charge is <=C and obeys this bound. This is sufficient below.
* Kannan fixed-dimension integer feasibility is imported from the previously source-checked parent theorem. Its use here is feasibility with bounded integer variables; witness coordinates are recovered through bounded decision queries. This lane did not newly inspect the primary paper.
* The normalform lane's sharper instruction bound3C+(2k-1)=O(k^3) can reduce dimensions, but the FPT theorem and crude bound below do not depend on it.

Governing system: finite exact integer/rational arithmetic and finite enumeration, plus the imported deterministic integer-feasibility algorithm.

## 2. Signed-power separation lemma [proved here]

Let S=sum_(i=1)^m epsilon_i 2^(e_i), with epsilon_i in{-1,+1}, e_i integers, and m<=M. Repeated terms are retained as separate occurrences. Choose H with2^H>M. Sort the occurrences by exponent and split whenever two consecutive exponents differ by at least H. Within a cluster all consecutive gaps are in{0,...,H-1}.

**Zero criterion.** S=0 iff every cluster has sum0.

Proof. For the lowest cluster G, write A=max exponent in G and B=min exponent in the next cluster. Its absolute sum is at most M2^A<2^B. The sum of all other clusters is an integer multiple of2^B, including when B is negative. If the total is0, the sum of G is such a multiple too, and hence is0. Remove it and repeat. The converse is immediate. The final single cluster needs no separation argument.

Each cluster's signed value relative to its minimum exponent depends only on its internal integer gaps. Its relative exponent span is <=(m-1)(H-1). Thus whether it vanishes can be decided by finite integer arithmetic whose size is independent of the absolute exponents.

**Integrality criterion.** Add a distinguished coefficient-zero anchor at exponent0 before clustering. Then S is an integer iff every cluster strictly below the anchor cluster sums to0 and the anchor cluster has integer sum. Clusters strictly above it are automatically integral.

Proof. If G is strictly below the anchor cluster, the next cluster's minimum B is <=0. Every integer and the sum of all terms above G are integer multiples of2^B. If S is an integer, G is therefore an integer multiple of2^B. Its absolute value is <2^B, so it is0. Peel the lower clusters in order. In the anchor cluster, all exponents relative to0 are fixed by the internal gaps, so integrality is a finite exact rational test. All clusters above the anchor have positive integer exponents. This proves necessity and sufficiency.

The strict margin2^H>M matters. For example two copies2^0 minus2^1 sum0, but an invalid H=1 split puts the lower and upper terms into distinct nonzero clusters. The admissible safe choice below is larger.

## 3. Symbolic bounded programs

Enumerate all instruction skeletons of length<=L(k), fixing operation types, row indices, add signs, and the permutation/rows of the2k-1 markers. Keep skeletons with charge<=C, exactly one marker per prescribed target, and distinct source/destination rows. Every shift/add exponent is a nonnegative integer variable; its value is not enumerated.

Replay each skeleton symbolically over rational functions of powers of two. Every scalar matrix entry at every prefix has the form

    sum_i epsilon_i 2^(E_i(x)),

where E_i is an integer affine form in the exponent variables. Left/right shifts add/subtract their exponent variable. An addition unions the old-destination and shifted-source occurrence lists, changing signs as specified. Explicit negation flips signs. Thus each scalar entry has at most2^A occurrences, where A is the total number of additions in the skeleton. Since A<=C<=27k^3, use the safe global values

    M = 2^(27k^3)+1,     H = 27k^3+2.

The extra occurrence allows the subtraction of one fixed target coefficient. Every nonzero normalized F2 coefficient is exactly a signed power of two with fixed exponent O(k^2); zeros require no occurrence.

Impose integrality of every scalar entry at every prefix, not merely at markers. For each marker and final identity entry, subtract the required exact coefficient and impose a zero equation. Rational elementary operations remain invertible, so no row can vanish identically; prefix integrality guarantees legality of every right shift.

For each scalar constraint, enumerate:

1. a permutation of its labeled exponent occurrences, including the0 anchor for integrality;
2. for every adjacent pair, either an exact small gap in{0,...,H-1} or a large gap>=H.

These choices are linear equalities/inequalities in x. Repeated exponent values are permitted by gap0; duplicate permutations do not harm correctness. Reject patterns whose finite cluster sums fail the zero/integrality tests of Section2. Each accepted pattern is then exactly characterized by its linear integer constraints. Taking the conjunction across scalar constraints and enumerating their finite pattern combinations gives a finite union of integer linear systems.

Completeness: any concrete legal bounded program induces one of the enumerated skeletons and one true sorted-gap pattern per scalar constraint. Soundness: an integer solution of any retained system has every required integral prefix and exact marker/final coefficient.

## 4. Both history scanners are linear feasibility constraints

Introduce integer upper-bound variables U^(r)_(t,i) for row i after step t, for r=0 and r=k-1. Initialize them to the exact scanner starts (0,...,0,r). For each operation impose:

* add(d,s,epsilon,h): Unew_d>=Uold_d+1 and Unew_d>=Uold_s+h+1;
* left(d,h): Unew_d=Uold_d+h;
* right(d,h): Unew_d=Uold_d-h;
* neg(d): Unew_d=Uold_d+1;
* unchanged rows and markers: equality across the step.

All U are nonnegative. Cap every r=0 variable by a and every r=k-1 variable by a-d+k-1. Impose d<=a<=n-2. Every exponent variable may also be capped by a: in a genuine capped scan, a left shift or right shift has size<=a, and an addition exponent is<=a-1.

**Why relaxed max inequalities are exact for feasibility.** A genuine scanner assignment satisfies the system with its actual widths. Conversely, every integral row prefix obeys the usual coefficient-mass invariant sum_j|X_ij|<=2^(u_i). An exact right shift by h of a nonzero integer row implies u_i>=h, since its divided row still has integer mass>=1. Hence actual scanner right shifts never clip. Starting from the exact initial widths, induction through addition inequalities and shift/negation equalities proves actual widths<=U at every step. Thus any feasible upper-bound assignment certifies both actual history caps.

No max branch or equality-to-maximum is guessed. Unrolling all max-plus paths is an alternative, but unnecessary. With the accepted L=O(k^4), this version uses O(kL)=O(k^5) integer variables; the sharper primitive bound would make this O(k^4). Both depend only on k.

## 5. Constructive FPT algorithm and runtime

For a proposed upper bound A<=n-2, add a<=A to each retained system and run fixed-dimensional integer feasibility. Accept iff at least one system is feasible. Sections3–4 and the imported bounded-witness theorem prove equivalence to the original arbitrary-helper threshold query.

First test A=n-2. If infeasible, return theta>n-2. Otherwise binary-search A in[d,n-2]. At the minimum A, take a feasible system and recover each coordinate by bounded binary decision queries. Exponents and a lie in[0,n]; scanner variables lie in[0,n+k]. The recovered skeleton and exponents are a complete realizing table. Exact algebraic legality is certified by the accepted exponent-cluster pattern; expanded intermediate matrices are not needed during the search.

There are finitely many skeletons, depending only on k. There are poly(k) scalar constraints, each with at most M+1 labeled terms. A loose pattern count is

    ((M+1)! (H+1)^(M+1))^poly(k)
      = 2^(2^O(k^3)).

The finite cluster tests use integers with at most O(MH) bits. Each retained ILP has a number of variables polynomial in k and an input length bounded by a k-only quantity plus O(log(n+1)). The imported integer-feasibility bound and bounded witness recovery therefore give

    time <= 2^(2^O(k^3)) poly(log(n+1)),

with an absolute polynomial exponent on log(n+1). This is a deliberately loose theoretical bound, not an implementation or practical running-time claim. It returns a compact instruction witness. If all intermediate integer matrices must also be printed explicitly, their O(n)-bit coefficients add expansion cost polynomial in numeric n; the requested numeric-n convention permits this.

This is FPT in k alone. It improves the prior XP bound whose exponent on n depended on k. It also differs from notes/constrained_table_optimization_complexity.md, whose FPT statement parameterized BOTH k and coefficient/width overhead Delta and used a different declared cost/width contract. Here the exact present scanner is retained and a is an unbounded optimization variable, bounded only by the requested n.

Nothing here makes2^(2^O(k^3)) polynomial in k or n. Combining it with the accepted outer algorithm therefore does not close the requested uniform growing-K P theorem.

## 6. Falsification record and checks

The preliminary balanced sign-gauge min-cut premise fails on the complete k=2 control row0-=row1; mark(-1); row0+=row1. Its two opposite preferred interaction signs and row timeline edges form a frustrated cycle. This blocks that specific balanced-graph reduction. It establishes no hardness result and no obstruction to another whole-table replacement.

PREREGISTRATION.2026-10-15T185500.md preceded the cluster tests. cluster_checks.2026-10-15T185600.py and CLUSTER_CHECKS.2026-10-15T185600.json record:

* 579,195 exhaustive signed sums, lengths0..5, exponents-3..3;
* 10,000 seeded random sums, up to30 occurrences, exponents-60..60;
* 44 structured carry/anchor cases, including up to2049 occurrences;
* 100 legal closed traces at k2..5, 200 endpoint scans, 12,000 scanner-update checks with deliberately slack upper bounds;
* an explicit deliberately insufficient-gap counterexample.

All passed. These are implementation checks for the lemmas, not a run of the enormous ILP threshold algorithm. The refutation lane independently reported20,000 exact Fraction cluster tests passing. The parent should attach its final independent review before promotion.

## 7. Assumption and consequence ledger

| Assumption | Use | Status |
|---|---|---|
| Integer distinct-row dyadic DSL, invertible prefixes | Symbolic exponent representation; nonzero-row/no-clipping proof | retained |
| Exact F2 integer normalization | Fixed signed-power marker constants | retained |
| Arbitrary helpers/order and identity endpoints | Enumerated complete skeletons and exact constraints | retained; no restricted family substituted |
| Charge<=27k^3 and accepted polynomial witness bound | Parameter-only occurrence, length, and dimension bounds | imported; applies to present profile minima |
| Two scanner endpoint characterization | Correct canonical cap(a,a-d) | imported; applies to all residues |
| Fixed-dimensional integer feasibility | Finite disjunction solver and coordinate recovery | imported; prior source validation |
| Numeric n objective convention | Permits explicit witness replay/expansion when desired | retained; compact algorithm has stronger log(n) dependence |

Immediate consequence: finite signed-power identities of bounded circuit size are representable by a finite, parameter-bounded disjunction of linear integer systems. The gain comes from exact cancellation and integrality clustering, not from bounding the numeric exponents by a k-only guess. The unresolved step toward uniform P is replacing the enormous skeleton/pattern enumeration with a polynomial constructive representation or a different global optimization theorem.
