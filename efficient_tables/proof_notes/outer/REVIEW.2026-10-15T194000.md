# Independent adversarial audit: polynomial witnesses and conditional polynomial outer planning

Verdict: **NO BLOCKING MATHEMATICAL DEFECT FOUND in the four reviewed statements, with the numeric-n and supplied-catalogue qualifications retained.** The polynomial witness/charge-bound results survive review. The outer optimizer is polynomial in physical operand width n, growing K, and catalogue input length once a complete minimum-charge catalogue is supplied. The end-to-end deterministic polynomial synthesis claim remains OPEN.

This review was independent of authorship but had access to the full proofs. It is explicitly NOT a blinded HG7 refutation pass. No Lean formalization is asserted. No local inference was used. Only new files in review_astra were written.

## Reviewed artifacts and provenance

Paths are relative to gap_closure_2026-10-15.

| Artifact | SHA-256 |
|---|---|
| profile_astra/POLYNOMIAL_WITNESSES.2026-10-15T151500.md | 04fdd1ee93364393407c2959d7a3a7ed84e61a7e557c331c70e69819f7eaa0d4 |
| profile_astra/CHARGE_STAIRCASES.2026-10-15T152500.md | 15a1a5c6df8848443ffa3fb6da40c847b070d3fb89959a78315b828fe070a85f |
| profile_astra/XP_REALIZATION.2026-10-15T153000.md | ac14e7aaa3bc112de31a11fac43b3080e8e2958318c3083c7800509c4d28f7bb |
| planner_astra/OUTER_ILP_REDUCTION.2026-10-15T144200.md | 7d3ba5b6b41cbd5d33652903613d0fb36fe298aea780322981a7424857da5ed7 |

Supporting imports read: fixed_execution contract plus addendum; BRIDGES and paired constructor bounds; PROFILE_THEOREMS plus addendum; FINITE_PROFILE_REDUCTION; packet17 Tcount.lean; the realizable-catalogue adversarial report. Falsifiers were registered in PREREG.2026-10-15T193600.md before independent computational tests, after reading the proofs.

## 1. Potential and polynomial witness result

The potential Phi=sum(u_i)-log2|det X| is valid. Distinct-row additions and negations preserve determinant magnitude; shifts change its log by exactly their signed amount. Every row remains nonzero, so the mass bound and coefficientwise exact right division imply u_i>=s before division by 2^s. Thus the scan never clips on a legal right shift. The potential increment is exactly 1 for negation and 1+max(0,u_src+s-u_dst) for an addition. Identity endpoints cancel determinant scaling. This proves t<=ka and t<=kb+(k-1)^2, without a helper restriction or fixed marker order.

Compression at charged operations AND markers is essential and is correctly done. A shift-only block is diagonal scaling; its net right shift is legal because the old block endpoint is integral. Endpoint matrices and current scan vectors agree, while history peaks can only decrease. Free prefix excursions then restore the canonical pair (a,b), preserving the balanced width function at every width. This does not promise preservation of the original arbitrary-vector raw influence profile; the claimed canonical planner profile is what is needed and what is preserved. Exact negative-fraction markers are unchanged because they remain separators with identical matrix states.

The bounds on exponents and coefficient bits follow from the w=0 cap and no-clipping lemma. The resulting NP and FP^NP statements are sound for numeric/unary a and n, not for binary a/n merely because exponents have short syntax. The charge-minimum O(k^4)-instruction witnesses do not provide a polynomial algorithm for finding them.

## 2. Charge staircases, k=2, and XP realization

The uniform minimum-charge ceiling follows from an actual constructor above the threshold a*=max(a0,b0+d), and from c<=3ka below it. The paired construction includes the two charged marker negations at even k for negative reciprocal points. Its bounds a0,b0<=8k^2 and c0<=6k^2 are applicable to the repository convention; the source proofs do not silently switch to the addition-only sign equivalence. The relaxed 27k^3 ceiling is valid.

The k=2 catalogue argument also survives review. For b<=1 the potential bounds charged instruction count by three. An even number of negations either leaves too few additions or is zero. At most three transvections producing a positive diagonal matrix cannot mix orientations. If all additions target row1, its e1 coefficient remains positive and cannot yield (1,-1). If all target row0, the weighted row-mass invariant for initial widths (0,1) gives mass 3 at target (1,-1), so its width is at least 2. At least one later row0 addition restores e1 coefficient zero; the net row0 scale between marker and final identity is zero because its e0 coefficient is 1 at both endpoints. Its final width is therefore at least 3, contradicting b<=1. The charge-four example attains (2,2), and padding covers precisely the remaining canonical feasible pairs.

For a fixed kink d, minimum charge is nonincreasing in a, so each charge equality set is one interval. There are polynomially many possible charge values but their thresholds need not have a proved polynomial-k location. Retaining the free padding variable is necessary: replacing a chosen width by a narrower threshold witness can change continuation costs. The XP enumeration and polynomial-space statement follow from the finite alphabet and O(k^4) witness length. Its k-dependent exponent does not establish uniform P.

## 3. Outer ILP reduction

The decorated-word bound is correct. With B(k)<=28k^5 and q=2k-1, the displayed sum is below 1, so the geometric series bounds all words with product q<=U by fewer than 3U^10. No fixed-K assumption enters. The generator may scan possible k values up to K, which adds only a polynomial-K factor.

The distinct-arity bound is decisive: t!<=product_distinct(2k-1)<=U implies t log t=O(log U). Thus t^{O(t)} becomes U^{O(1)}. A dimension bound by depth alone would not suffice; the proof correctly uses distinct arities.

There really are only t integer variables a_k. The x_i and w_i symbols are substituted affine expressions. For each i, all increments after its own increment are multiples of P_(i+1), so x_D=P_D z implies x_i-P_i r_i is divisible by P_(i+1). Hence w_i is integral with residue r_i modulo k_i. This checks all residues, including the root and repeated occurrences. The inequality k_i*x_i-x_(i+1)>=P_(i+1) is exactly w_i-w_(i+1)>=1. Positive terminal z plus these inequalities establishes every width in [1,n].

The local objective has exactly the required N_i multiplicity. P_D clears every denominator, with polynomially many bits because P_D<=N_D<=U. One fixed a,d,c per arity gives one fixed profile; the supplied witness selected once for that profile can be reused at every occurrence. Minimum charge at that profile is sufficient by the exact-padding replacement theorem. The enumeration is complete for all competitive ladders, and sound for the actual prescribed F2/common-child model.

## 4. Primary-source ILP theorem and reconstruction

Primary source: Ravi Kannan, *Minkowski's Convex Body Theorem and Integer Programming*, Theorem 5.4, printed page 432, with preprocessing in Section 5, pages 430–431. Source URL: https://www.math.ucdavis.edu/~deloera/MISC/LA-BIBLIO/trunk/Kannan/Kannan1.pdf . Parent fetched coordinator/Kannan1987.source.pdf; independently checked SHA-256 408174c9db49c35050e84775e42e85a6b7499d335798b8ec1cbb0778631834c8 and visually inspected coordinator/Kannan1987.page16.png, page17.png, and page18.png.

The theorem bounds arithmetic operations by O(t^(9t/2)*s), and intermediate integer bit size by O(t^(2t)*s), with s input length. Elementary polynomial-bit arithmetic therefore gives t^{O(t)}*poly(s) bit time. The potentially exponential-in-dimension integer sizes are acceptable here: t^{O(t)} is already polynomial in U. No Frank–Tardos improvement is needed for this conclusion. Section 5 explicitly preprocesses lower-dimensional feasible sets, so the terminal equality does not violate the full-dimensionality premise of an internal subroutine.

Minor presentation clarification: The quoted procedure is a decision algorithm. The planner need not import native witness recovery: every a_k is bounded in [0,n-2], so O(t log(n+1)) coordinate-bound feasibility queries recover a feasible integer tuple while fixing previously recovered coordinates. This preserves t variables and polynomial runtime. No extra integer slack variables are needed to encode equalities or costs; paired inequalities suffice.

## 5. Exact leaf formula and encoding

The source Tcount.lean defines tau using exact real constants 3.075=123/40 and 0.86=43/50, and explicitly uses round_eq x = floor(x+1/2). Thus tau(R)=floor((615 log2(100R)+272)/200) for positive R. Integer bit length of (100R)^615 gives the exact value, including threshold cases; the fixed exponent gives polynomial bit complexity. Positive terminal widths ensure reached R>=1. The empty ladder handles n=1 and any instance with no legal recursion. The upper bound U=O(n^2 log(n+1)) and product-call bound are valid.

All resulting polynomial statements are in physical n, growing K, and explicit catalogue length. They do not establish polynomial time in log(n). The benchmark is PP only; no analogous PTP leaf formula is imported. The output is exact for the common-child planner, not the distinct-width KMY estimator.

## 6. Independent finite checks

INDEPENDENT_CHECKS.2026-10-15T193700.json records PASS:

* 86 closed programs, using a newly written exact replay/determinant implementation rather than importing author test functions.
* Six complete F2 marker programs at k=2,...,7, including even-k negative reciprocal repository signs; arbitrary-marker reset constructors were generated independently.
* 3,096 balanced-width replays tested determinant potential increments, row-mass/no-clipping, exact markers, net shift compression, restored profile padding, and witness instruction bounds.
* 110,000 decorated affine assignments for arities 2 and 3, depths 1–3, offsets 0–3, all legal kinks/residues, n=1–16.
* 8,832 assignments satisfying terminal integrality, including 6,560 repeated-arity assignments, agreed exactly with direct recursive widths, residues, and contraction predicates.

The deterministic test source was executed inline in the recorded tool transcript, seed 193600. The JSON is retained; no claim is made that author scripts were independently rerun or that these finite domains prove the universal statements.

## 7. Scope of the outcome

Accepted: polynomial witness length; polynomial range of minimum charges; polynomially many staircase descriptors; XP realization; uniform polynomial exact outer optimization conditional on a complete minimum-charge catalogue or a polynomial realization/value oracle with reconstruction.

Still OPEN: a deterministic polynomial algorithm that actually constructs the unrestricted arbitrary-helper minimum-charge catalogue; a full end-to-end growing-K P/FP theorem; the stronger binary-n bound; any universal monotone-arity normal form for unrestricted all-table optimization.

The adversarial report refutes monotone/contiguous simplifications for specified realizable catalogues. It does not refute the user's conjecture for the unrestricted universe of all legal F2 tables. Neither those examples nor this audit provide a hardness result.
