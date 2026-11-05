# Exact k2 realization and polynomial charge staircases

Status: analytical derivations and exact checks, pending independent review. Main uniform polynomial synthesis remains OPEN. These results supplement POLYNOMIAL_WITNESSES.2026-10-15T151500.md. Scope/imports are identical. Coordinator supplied the uniform charge-range deduction; the profile agent checked and expanded it.

## 1. Complete k2 profile catalogue

For k=2 and fixed F2 PP targets0,infinity,-1, a canonical pair(a,b) is feasible iff b>=2 (equivalently a>=2 and b>=2). Every feasible pair has minimum charge4, realized by

    mark row0=0; mark row1=infinity;
    row0 -= row1; mark row0=-1; row0 += row1,

followed or preceded by the free identity padding to the requested profile. The base profile is(a,b)=(2,2), with c=4.

Why charge<4 is impossible at any width: restoration and a nonbasis marker require at least two additions, since zero additions never change support and one addition's new offdiagonal coefficient cannot be removed by unary row scaling/sign changes. If c<=3 contains a subtraction, there is room for only that one addition. Otherwise all additions are positive. Determinant sign restoration forces an even number of negations. Zero negations cannot produce a negative target entry; two negations leave budget for at most one addition. Each case is impossible.

Why b<=1 is impossible even at unlimited charge: the potential theorem bounds t<=2b+1<=3. Negation count is even. With two negations there is room for at most one addition, already impossible. Thus there are no negations and at most three additions. Delete all free shifts by viewing the row operations over Q: diagonal scalings can be commuted to the end, leaving at most three elementary transvections with nonzero signed-dyadic multipliers; the accumulated diagonal at the end has positive diagonal entries. If the original product is I, this transvection product must be diagonal. With at most three transvections in two dimensions, a mixed-orientation product cannot be diagonal: U(x)L(y) has offdiagonals x,y; U(x)L(y)U(z) has lower-left y; cases with adjacent equal orientations combine to two factors, and a cancelled pair leaves one nonzero offdiagonal. Therefore all additions have the same destination.

If that destination is row1, its row1-coordinate remains a positive dyadic unit, so it cannot equal target(1,-1). If the destination is row0, at the target the scan with initial vector(0,1) must have row0 width at least2. Explanation: row1 remains a positive dyadic multiple2^e e1, its scan is1+e, and every row0 addition creates influence from the top coordinate. At the marker's primitive top coefficient-1, that influence must have coefficient magnitude1 and the addition scanner contributes an extra bit; equivalently the row0 influence from top is at least1. Restoring row0 requires a subsequent row0 addition, whose own +1 increases its width after accounting for intervening scalings. Since its e0 coefficient is1 at both marker and final, the net row0 scale between them is zero (row1 has no e0 component), so unary shifts cannot erase this extra unit. Hence final row0 width is at least3 and the history cap at remainder1 is at least3, forcing b>=2.

The last step may also be phrased with normalized row0 width u0−log2(coefficient of e0): every source addition increases this quantity by at least1; at target its top contribution forces normalized width>=2; restoration needs one more addition; final e0 coefficient1 restores the normalization. This argument allows arbitrary free shift excursions and exact divisions.

Exact cap graph checks independently exhausted(a,b)=(1,1):21 states and(2,1):66 states, finding no feasible table. At(2,2), Dijkstra found optimum4 after203 expansions,286 discovered states. The unbounded small-proof argument above, not a fixed shift cutoff, establishes the catalogue.

## 2. Every feasible minimum charge is polynomial in k, independent of a

Use the prior positive-first paired F2 constructor, with canonical profile(a0,b0), charge c0, and the established bounds

    a0,b0<=8k^2,       c0<=6k^2.

For a canonical pair write d=a-b, so0<=d<=k-1 and a>=d. Let

    a*=max(a0,b0+d)<=8k^2+k-1.

If a>=a*, the constructor's profile is componentwise below(a,a-d); free padding yields the requested pair at charge c0<=6k^2. If a<a* and the pair is feasible, the potential theorem bounds EVERY realizing table by

    c<=3ka<3k(8k^2+k-1)<27k^3.

Thus every feasible minimum charge satisfies c_min(k,a,b)<=27k^3. The bound does not assert every feasible table above threshold has small charge, only that a suitable minimum-charge witness does.

This supplies short minimum-charge witness skeletons independent of numeric a: t<=c_min<=27k^3, hence at most(k+1)(27k^3+2k-1)+k+4=O(k^4) instructions. Exponents still may be as large as a, so replay arithmetic remains polynomial in numeric a. Encoded syntax has size O(k^4(log(k+1)+log(a+1))); that syntax-size statement alone is not a polynomial verifier in log(a).

## 3. A polynomial number of unknown staircase thresholds

Fix d in[0,k-1]. The function

    f_d(a)=c_min(k,a,a-d),       a>=d,

with infeasible values +infinity is nonincreasing. Indeed enlarging a by1 enlarges both cap coordinates, preserves feasibility, and padding transforms any old realization into the new exact profile at equal charge. Once finite, values belong to the integer set[0,27k^3]. Hence there are at most27k^3+1 distinct finite plateaux, plus an initial infeasible interval. There are k rays, giving O(k^4) finite plateau descriptors per arity.

Each descriptor records the first a attaining a given improvement. For any finite query range a<=n-2, these thresholds and a witness at each can be found with polynomially many NP-oracle calls: query whether a charge bound C is feasible at a; along a ray the answer is monotone; binary search the smallest a<=n-2 for each C=0..27k^3. This uses O(k^4 log(n+1)) decision calls, each verified in polynomial numeric n,k by the witness theorem. Duplicate thresholds may be discarded.

Crucial limitation: a threshold witness has the smallest width for that charge level. Replacing an arbitrary larger profile by it can change recursive child widths, and continuation costs are not assumed monotone. To preserve an original recursion exactly, its descriptor must retain the free padding parameter a, and construct the padded table at that requested a. Therefore these are polynomially many CHARGE-function descriptors, not a proved finite list of unpadded tables preserving every global optimum. The repeated-arity rule remains binding. Charge plateaux could begin at very large a; no polynomial-k upper bound on every improvement threshold is proved.

## 4. Tests and remaining gap

Preregistration: PREREGISTRATION_BOUNDARIES.2026-10-15T152000.md. Script and output: boundary.2026-10-15T152100.py and BOUNDARY.2026-10-15T152100.json. The three complete tiny graph queries above finished without cutoffs. The numeric inequality3k(8k^2+d)<27k^3 passed500499 integer cases k2..1000,d0..k-1. Universal statements use the proofs, not these finite checks.

No polynomial deterministic method is known here for finding the staircase thresholds or the arbitrary-helper charge-minimal witnesses. The potential/charge ceiling and staircase compression substantially narrow certificate and value-domain questions, while the uniform P/FP target remains unresolved.