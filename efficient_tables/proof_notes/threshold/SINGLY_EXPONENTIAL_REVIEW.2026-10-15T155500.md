# Review addendum: singly exponential constructive threshold algorithm

Status: independent proof-visible review of the coordinator's combination of the saturation lemma, constructor budget split and primitive macro search. No blocking defect found. This supersedes the doubly exponential factor as the best reviewed upper bound in this lane; it does not supersede the exact scalar cluster reduction used to prove saturation.

## 1. Parameter-only search cutoffs

Let c0(k)<=6k^2 and(a0,b0), with a0,b0<=8k^2, be the actual accepted paired-constructor charge/profile. For fixed0<=d<k define a*=max(a0,b0+d)<9k^2.

If C>=c0, a complete witness exists under ray cap(a*,a*−d), by free padding. Thus the exact threshold is no larger than a*. A smaller cap can use an entirely different table and more charge; the algorithm still searches all legal normalized words up to budgetC and does not constrain them to the constructor family.

If C<c0, the reviewed symbolic small-integer-point reduction gives a k-only cutoff

    S(k,C)=(t+1)t!B^t,

where t<=2C+1 and B is an explicit polynomial bound on the symbolic constraint coefficients/right sides, independent of n. As C<6k^2, log S=O(k^2 log k). Every finite threshold is <=S. The proof uses symbolic clusters and the small-point lemma; the algorithm below does not enumerate cluster patterns itself.

For a truncated query use A=min(n−2,a*) in the high-budget case and A=min(n−2,S) in the low-budget case. If A<d, report theta>n−2 immediately. If A<S in the low-budget case, failed search proves only theta>A, not global infinity. If the full cutoffS is searched and no witness exists, no finite threshold exists.

## 2. Exact constructive macro enumeration

At primitive boundaries a state consists of the exact integer row matrix, the two current scanner vectors, the two accumulated peaks and a bitmask of covered required targets. Automatically cover each newly visible exact F2 target at its first occurrence. Because marker order is unrestricted, markers have no effects/cost, and all required vectors are primitive, this retains completeness. Return an explicit marker instruction at each first occurrence to obtain a literal complete table.

Enumerate every macro word of charged cost<=C. For an addition choose distinct destination/source rows, sign, and p,q>=0 with min(p,q)=0, p,q<=A−1. Form

    Z=2^p Y_dst+sign*2^q Y_src,

check both transient pre-division cap tests, and divide the changed row by its maximal common power of two. The valuation is determined from the integer row; it is not an additional branching variable. Include negation macros. Every macro costs at leastone, so word length is at mostC. Reject nonintegral/invalid prefixes through the exact macro implementation; retain only endI states covering all targets.

For each complete retained word compute its actual canonical profile(a_word,b_word). Its least ray cap is

    max(d,a_word,b_word+d).

Take the minimum over the enumerated words. This is exact, because normalization preserves charge and never raises either cap, and every genuine optimum below the chosen cutoff has a normalized representative in the enumeration. Alternatively binary-search caps and retain a witness; both methods are valid. A cap witness need not attain its cap exactly. If an exact profile is needed later, the existing four-shift padding lemma supplies it at no additional charge.

## 3. Runtime

The branching count is O(k^2(A+1)). At mostC paid macros are explored per word. Under the cap, matrix coefficients have O(A) bits, so exact replay and target comparisons cost polynomial(A,k). Marker saturation adds only polynomial factors per prefix; it does not introduce an independent order permutation factor.

For C<c0, A<=S=2^{O(k^2 log k)} and C=O(k^2), hence

    (k^2(S+1))^O(C) poly(S,k)
       =2^{O(k^4 log k)}.

For C>=c0, A<9k^2 and C<=27k^3, hence

    (k^2(A+1))^O(C) poly(A,k)
       =2^{O(k^3 log k)}.

Reading/comparing n and applying its truncation adds polynomial(log(n+1)) time. Therefore the combined exact threshold-and-witness algorithm has the uniform parameterized bound

    2^{O(k^4 log k)} poly(log(n+1)).

This is a compact instruction witness bound. The generated exponents are at most the k-only cutoff, so even explicit row replay fits inside the displayed parameter factor. The algorithm is theoretical and enormous; this lane did not implement its full enumeration.

## 4. Consequence and boundary

The accepted outer shared-table theorem needs O(k^4) threshold queries per arity, followed by polynomial(n,K) work. Multiplying by the threshold algorithm and summing arities up toK yields

    2^{O(K^4 log K)} poly(n)

for exact recursive optimization and a consistent one-table-per-arity witness family, under the retained numeric-n convention. Repeated arities are handled by the already accepted outer theorem; the local synthesis algorithm does not relax their shared-table requirement.

Neither singly exponential FPT nor k-only saturation is polynomial in growingk. The requested uniform P result remains open. The next missing theorem is a polynomial search/replacement principle that removes the exponentially many macro words; a polynomial saturation bound alone would still not remove that enumeration.

This review is independent with author/coordinator reasoning visible, not blind HG7. No new cap graphs, local inference or old-file edits were used.
