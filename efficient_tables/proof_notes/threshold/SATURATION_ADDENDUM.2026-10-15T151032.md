# Independent saturation and singly exponential FPT audit

2026-10-15. Addendum to INDEPENDENT_REVIEW.2026-10-15T150700.md. Reviewed the full `../algorithm_astra/SATURATION_AND_SINGLE_EXP_FPT.2026-10-15T190800.md` after independently deriving the homogenized-cone small-point proof and coefficient bounds in messages to the coordinator and author.

**Verdict: no blocking mathematical defect found.** Accept the finite-threshold saturation bound and its constructive consequence:

    m=6k^2, B=8k^2, S(k)=(m+1)m!B^m,
    theta finite implies theta<=S(k)=2^O(k^2 log k),
    threshold computation with a complete witness:
        2^O(k^4 log k) poly(log(n+1)).

The new threshold algorithm uses elementary finite normalized-word search. It does not need to execute Kannan's algorithm or enumerate the enormous collection of symbolic pattern systems. The latter establish the saturation bound only. The accepted OUTER shared-table optimizer retains its separate integer-programming import. The uniform growing-K polynomial-time claim remains OPEN.

## 1. Small-point lemma: independent derivation and edge cases

For an integer system P={x>=0:Ax<=b} in t variables with all coefficients and right sides bounded by B>=1, homogenize to

    K={(s,x)>=0:Ax<=bs}.

K lies in the nonnegative orthant and has no line. Its intersection with s+sum(x_i)=1 is a compact polytope. Repeatedly decomposing a nonvertex point along a line in its minimal face yields a convex combination of vertices; each decomposition reaches smaller faces because the slice is bounded. Those vertices correspond to extreme rays of K.

An extreme ray in ambient dimension t+1 has t linearly independent active homogeneous normals. If their rank were lower, a second independent kernel direction would give a small two-sided perturbation respecting every inactive strict inequality and contradict extremality. This argument works when K is lower-dimensional: its affine-hull equalities contribute to the active-normal rank. Cofactors of any such t-row matrix give a nonzero integer generator; choose its sign in the nonnegative orthant and divide by the gcd. Every coordinate is at most D=t!B^t.

A generator with s>0 gives a vertex v of P after dividing x by s. Since s is a positive integer, every coordinate of v is at most D. A generator with s=0 is an integer recession ray r whose coordinates are also at most D. Decomposing (1,z), for any integer z in P, gives a convex combination v_bar of such vertices plus a nonnegative combination of recession rays. The recession part can be reduced to at most t rays by eliminating linear dependences while keeping coefficients nonnegative.

Write z=v_bar+sum_(j<=t) lambda_j r_j and subtract sum floor(lambda_j)r_j. The resulting y is integer, remains in P, and satisfies

    0<=y_i<=D+tD=(t+1)t!B^t.

This is the same bound as the author's proof. The author obtains the slightly sharper recession-ray cofactor bound (t-1)!B^(t-1) directly in ambient dimension t; that proof is also valid. My homogenized derivation avoids needing the sharper bound and independently confirms the stated constant.

Checked edge cases:

- Lower-dimensional P and recession cones: active constraints include their defining equalities; full-dimensionality is not required.
- Bounded P: there are no recession rays, and the vertex-coordinate bound already suffices.
- t=1: the direct ray proof uses the empty minor equal to one, as the author states.
- Fractional vertices: permitted, because the original integer point minus integer ray multiples remains integer; v_bar need not itself be integral.
- Integer ray scaling: essential. One may not subtract floors times an arbitrarily normalized rational ray.
- Arbitrarily many inequalities: irrelevant to the determinant bound; only t independent active normals determine a ray or vertex bound. The proof still requires a finite system, which every skeleton/pattern supplies.

A concrete lower-dimensional check illustrates the lattice issue. In R^3 let 2x-y=1, z=3x, with nonnegative coordinates. The vertex is (1/2,0,3/2), the primitive integer recession ray is (1,2,3), and the integer point (1001,2001,3003) equals that vertex plus (1000+1/2) times the ray. Subtracting 1000 integer rays leaves the feasible integer point (1,1,3). Dividing that ray by two before applying the floor operation would not in general preserve integrality. The reviewed proof uses integer rays correctly.

## 2. Dimension and coefficient accounting

The primitive normal form has raw addition

    2^p Y_d + epsilon 2^q Y_s, min(p,q)=0,

followed by its exact common-power division. If p>0, the source has an odd entry and the destination term is even, so the raw sum is primitive. If q>0, the destination has an odd entry and the source term is even, with the same conclusion. Only p=q=0 permits a nonzero normalization valuation.

Thus each addition has precisely one of these template types:

1. A shifted-source add with exponent h>=1.
2. A destination left shift h>=1 followed by an unshifted add.
3. An unshifted add followed by an exact right shift h>=0.

Each type has one exponent variable. A additions plus the threshold coordinate a require t=A+1<=C+1 variables. Negations and markers add no integer variables. As an optional consequence, every addition needs at most two primitive instructions, improving the earlier conservative three-instruction bound; the final complexity claim does not depend on this extra observation.

Completeness follows from actual primitive-boundary witnesses. Soundness of a feasible symbolic system needs only an allowed complete table, not primitive macro boundaries. The system may therefore omit the condition that a guessed right shift removes the maximal common power. Every integral solution still gives legal prefix divisions, exact targets, identity restoration and scanner caps. It can be normalized again before the final finite search. This omission does not add invalid tables or break saturation.

For C<c0<=6k^2, integer C<=6k^2-1 and hence t<=m=6k^2. The signed-power clustering uses H=C+2 and M=2^C+1. Adjacent gaps, not telescoped whole-cluster spans, are constrained. Every exponent variable occurs at most once on each time-ordered symbolic path. Therefore differences of symbolic exponent forms have coefficients of magnitude at most two. A target exponent is less than k^2, so all adjacent-gap right sides have magnitude at most

    H+k^2<=7k^2+1<=8k^2.

Unrolling the two exact max-plus scanners introduces no extra variables. Every scanner path has exponent coefficients in {-1,0,1}; its constant is at most C+k-1. Comparing paths against a or a-d+k-1 keeps all right sides within B=8k^2. There is no hidden exponential coefficient from the potentially long relative span of a cluster: that span is used only to accept or reject the finite pattern.

Exact prefix integrality and invertibility still establish no right-shift clipping, so these unrolled paths encode the actual conservative scanner. They do not substitute coefficient magnitude for history peaks. Every retained system is consequently a finite polyhedron in a nonnegative orthant with the claimed m and B bounds.

## 3. Saturation and constructive search

For a finite low-budget threshold, normalize a witnessing complete table and select its actual template and cluster patterns. This yields an integer point of an uncapped retained system. The small-point lemma supplies another feasible integer point with a<=S(k). Since every integer solution of that system is a valid complete table, the finite threshold itself is <=S(k).

For C>=c0, the existing legal paired constructor has profile (a0,b0), charge c0, and a0,b0<=8k^2. Set a*=max(a0,b0+d). Then a*>=d, its cap contains the constructor, and a*<=9k^2. This high-budget bound is direct and does not need the polyhedral lemma. The source bounds were checked in the accepted gap-closure CHARGE_STAIRCASES §2.

The final algorithm compares binary n with S or a*, then runs normalized enumeration under cap T=min(n-2,S) or min(n-2,a*). Its real state arithmetic uses O(T)-bit coefficients, not unit-cost arbitrarily large integers. For low budgets C=O(k^2), log T<=log S=O(k^2 log k), so

    (k^2(T+1))^O(C) poly(T,k)=2^O(k^4 log k).

For high budgets T=O(k^2) and C<=27k^3, the bound is 2^O(k^3 log k). Binary search for the least feasible cap adds at most log S=poly(k) iterations. Reading and comparing n contributes poly(log(n+1)); the arithmetic search is parameter-bounded even if n is arbitrarily large. Infeasibility at the chosen truncated bound gives the correct answer theta>n-2. It is not necessarily a claim of global infinity when n-2<S.

Marker consumption at the earliest available primitive boundary is valid because marker order is free, marker cost is zero, and markers do not change rows or scanners. Both transient predivision scanner caps and final identity must be checked. Weighted charge must also be checked: positive add costs one, negative add three, negation one. I sent a minor exposition request to make this last check explicit in §7; its stated import of the already complete normalized budget enumeration enforces it. The count of at most C charged macros alone is a length bound, not a replacement for weighted-charge pruning.

The algorithm is constructive without any integer-programming subroutine. The symbolic systems need not be generated during execution. They prove the finite search bound; actual normalized-word enumeration reconstructs a realizing program and the minimum cap.

## 4. Scope, verification and remaining theorem

The refinement is an analytical theorem reviewed with the proof visible. No new full threshold implementation was run. The earlier independent Fraction/carry checks still support their narrow algebraic lemmas; they do not establish the new universal small-point theorem empirically.

I inspected the coordinator's `ThresholdAlgebraRepair20261015.formal.json`: it records five proved elementary integer/relaxed-scanner lemmas, zero sorries, and trusted replay. These cover separated and anchored cancellation, relaxed addition domination, legal right-shift domination, and one negative-exponent normalization inequality. They do not formalize the signed-power pattern construction, polyhedral saturation, full table semantics, finite-search complexity, or recursive optimization theorem. Those remain paper proofs with independent review.

The accepted sharper local bound combines with the existing outer theorem as 2^O(K^4 log K) poly(n) for the exact shared-table recursive optimizer under the numeric-n convention. Neither polynomial saturation in k nor polynomial-time search over charged skeletons has been proved. The growing-K uniform P target remains open.

All pre-existing artifacts remain unchanged. This is a new timestamped audit addendum, with no local model inference.
