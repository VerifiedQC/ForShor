# Whole-table primitive normalization and the remaining global gap

Status: analytical derivation with deterministic witnesses; independent review requested from the parallel refutation lane. No independent-review gate or uniform polynomial theorem is claimed here. Existing files are unchanged. The main threshold problem remains open.

## 1. Exact scope and outcome

Fix k>=2 and the exact repository F2 PP target set. Every legal complete table P has a constructible complete table N(P) such that:

1. Every marker has the same exact row, row index and order; the endpoints remain I_k.
2. Positive additions, negative additions and negations are individually preserved. Hence c=plus+3minus+neg is unchanged, including the negative-reciprocal convention at even k.
3. For EVERY nonnegative initial scanner vector, the replacement has no larger peak. In particular both required endpoint caps are preserved.
4. Between charged operations all rows are primitive: their entries have no common factor 2. An addition is implemented by at most one destination left shift, one addition of the original sign, and one exact right shift. No other shifts remain.
5. If A is the addition count and nu the negation count, the new length is at most 3A+nu+2k-1 <=3c+2k-1.

Consequently, using the already reviewed ceiling c_min<=27k^3, every feasible cap has a minimum-charge witness of at most 81k^3+2k-1 instructions. Add four free prefix-padding instructions if the exact original canonical profile, rather than merely its cap, must be restored. This improves the prior O(k^4) witness-length bound to O(k^3).

This theorem supplies a GLOBAL replacement of every closed table. It does not supply a polynomially sized or polynomially searchable family: the primitive helper matrices are still unrestricted.

## 2. Assumptions and applicability ledger

The governing axiom system is ordinary exact integer and rational linear algebra.

| Hypothesis/import | Use | Applicability |
|---|---|---|
| Start/end I and invertible row operations | Rows never vanish; endpoint valuations zero | Fixed contract |
| All intermediate rows integral; division exact | Common 2-valuations g_i are nonnegative; replacement divisions legal | Fixed contract |
| Every marker primitive | Removing row scale preserves exact marker | F2 integer markers have first coordinate 1; fraction markers have last coordinate 1, also for negative denominators |
| Scanner addition, negation and shift rules | Boundary identities and intermediate peak inequalities | CONTRACT plus PROFILE_THEOREMS |
| No-clipping lemma for legal programs from I | u_i>=g_i and subtraction represents right shifts exactly | PROFILE_THEOREMS §3; its nonzero/integral hypotheses hold |
| Existing c_min<=27k^3 | Uniform O(k^3) minimum-witness corollary | gap_closure RESULT §2; same cap and charge model |
| Free canonical padding | Four-instruction exact-profile restoration | PROFILE_THEOREMS §5; lower and top row exist because k>=2 |

No fixed row roles, special helper structure, prescribed order, target rescaling, or bounded determinant hypothesis is added. No external theorem is imported.

## 3. Constructive normalization proof

At any original instruction boundary let X_i be row i and

    g_i = min_{j:X_ij !=0} v_2(|X_ij|),     Y_i = 2^(-g_i) X_i.

For a scanner initialized at any fixed nonnegative vector, write its old current widths as u_i and define v_i=u_i-g_i. We maintain replacement matrix Y and current widths v. The existing row-mass invariant implies u_i>=g_i, so v is nonnegative. Initially g=0, X=Y=I and u=v.

An old left or right shift changes g_i and u_i by the same amount and leaves Y and v unchanged. Erase it. A negation changes Y_i to -Y_i and raises v_i by one; reproduce exactly the same negation. At a marker the row is primitive, g_i=0, so reproduce exactly that marker.

For an original add X_d <- X_d + epsilon*2^s X_h, define

    e=s+g_h-g_d,     u'_d=1+max(u_d,u_h+s).

The two cases are exhaustive.

### Case e>=0

Perform Y_d <- Y_d+epsilon*2^e Y_h, obtaining Z. Let t=v_2(gcd Z) and then divide row d by 2^t. This is legal by definition. Original X'_d=2^g_d Z, hence g'_d=g_d+t. The pre-division replacement width is

    1+max(v_d,v_h+e)=u'_d-g_d <=u'_d.

After division it is u'_d-g_d-t=u'_d-g'_d. Other normalized rows and widths are unchanged. Thus the invariant and the peak bound hold.

### Case e<0

Put p=-e>0. Left-shift Y_d by p, then add epsilon*Y_h with exponent zero, obtaining Z=2^p Y_d+epsilon Y_h. Let t=v_2(gcd Z) and divide by 2^t. Since p>0 and Y_h is primitive, actually t=0 in this case; retaining t in the formulas makes the common rule transparent. Original X'_d=2^(s+g_h) Z, so g'_d=s+g_h+t.

The intermediate left-shift width is

    v_d+p=u_d-s-g_h <=u_d.

The post-add/pre-division width is

    1+max(v_d+p,v_h)=u'_d-s-g_h <=u'_d.

After division the width is u'_d-g'_d. Thus all replacement peaks are bounded by old peaks before or after the corresponding instruction. The same algebra holds separately for EVERY scanner initialization; the replacement instructions do not depend on that initialization.

Induction establishes all five conclusions. Exact endpoint I has all g_i=0. At all charged boundaries the primitive rows are integral and nonzero. The construction is deterministic, using exact row arithmetic and valuations, with time polynomial in the explicit input program's arithmetic representation and output bit sizes. It is a witness transformer, not an algorithm for finding the optimum witness.

## 4. A smaller exact XP search

Normalize the search state to (Y,v^0,v^R,S), with R=k-1. All rows of Y are primitive. A macro addition chooses d!=h, epsilon in {-1,+1}, and p,q>=0 with min(p,q)=0:

    Z=2^p Y_d+epsilon*2^q Y_h,
    t=v_2(gcd Z),
    Y'_d=Z/2^t,
    (v^z)'_d=1+max(v^z_d+p,v^z_h+q)-t.

Its actual transient peak must pass BOTH cap tests BEFORE subtracting t:

    1+max(v^0_d+p,v^0_h+q)<=a,
    1+max(v^R_d+p,v^R_h+q)<=R+b.

The optional destination left shift is already bounded by the post-add peak. Under cap a, p,q<=a-1. A negation is one additional macro of cost one. Macro charge is one for epsilon=+1 and three for epsilon=-1. Consume any newly available exact target at the earliest normalized boundary, at zero charge. This loses no marker: a shifted nonprimitive row cannot equal a primitive target; an addition output with t>0 is also nonprimitive until the forced division.

There are O(k^2(a+1)) choices per charged macro, and a budget-C word has at most C macros. Search all such words, checking legality, both transient caps, coverage and final I. This is complete by the normalization theorem and sound by expanding each macro to legal primitives. For each k,d,C, binary search a in [d,n-2] uses cap monotonicity; retain a successful reconstructed macro word at the smallest feasible a. If the highest cap is infeasible, report theta>n-2.

Complexity is

    (k^2(n+1))^O(C) poly(n,k),

and therefore (k^2(n+1))^O(k^3) poly(n,k) for C<=27k^3. Coefficients have O(n) bits under the cap. This improves the older XP exponent O(k^4) to O(k^3), but its exponent STILL grows with k. It is not the sought polynomial(n,k) theorem.

## 5. Marker-free exact loops really are erasable

Suppose a contiguous marker-free segment starts and ends at the same exact matrix X. Because X is invertible, its total rational row-operation matrix is I. Let F be its max-plus scanner transfer matrix before any clipping. Inductively the rational coefficient matrix M of that segment satisfies |M_ij|<=2^F_ij (with 2^(-infinity)=0): an addition is bounded by twice the larger term, shifts rescale both sides and negations only increase the bound. Since final M=I, F_ii>=0. Hence the final width of row i is at least its initial width. The clipped scanner, if considered independently, is no smaller.

Delete the segment. The later algebraic rows and markers are identical, and the current width vector at reconnection is componentwise no larger; scanner monotonicity therefore bounds every later peak. Charge cannot increase. This also applies to a repeated primitive matrix at normalized macro boundaries.

This is exact loop erasure only. It does not authorize erasing an arbitrary helper excursion with a different final matrix, and does not bound the number of distinct primitive matrices on a loop-free path.

## 6. Determinant restrictions: local evidence is not global completeness

At primitive boundaries det(Y) is still a signed power of two; it need not be a unit. A macro with p>0 raises its 2-exponent by p, and a right normalization lowers it by t. This represents a genuine integer-lattice excursion after scalar row factors have been removed.

For z=2^e, e>=0, simultaneous integer marker rows v(+z),v(-z) have all 2x2 minors divisible by 2z, and the minor using columns 0,1 equals -2z. Their determinantal divisor is exactly 2^(e+1). Repository reciprocal pairs give the same divisor by column reversal (including their actual signs). Thus any integer matrix containing both rows has determinant divisible by 2^(e+1). Both rows individually are primitive.

This refutes the statement that primitive target-containing states automatically have determinant exponent <=1. It does NOT refute existence of a globally optimum closed table avoiding simultaneous target pairs. That stronger whole-table replacement statement remains unproved. No local coexistence example is being passed off as a global lower bound.

Moreover the prior Newton obstruction already uses primitive helper rows, so N1 does not evade that partial-state obstruction. The obstruction's narrow scope still matters: it does not refute a whole-table polynomial family.

## 7. Exact checks and audit boundary

PREREG.2026-10-15T145000.md fixed the tests before execution. primitive_check.2026-10-15T145100.py and PRIMITIVE_CHECK.2026-10-15T145200.json record:

- 57 complete F2 constructors: k=2..20, C1 and both pair orders.
- 500 seeded complete tables: k=2..7, random legal 20-operation prefixes followed by exact inverses and a complete C1 table.
- Every exact marker, I restoration, separate signed operation counts, every original-to-normalized boundary matrix and scanner identity, both endpoint peaks and one further arbitrary nonnegative initialization per case.
- 11,100 negative effective exponents; 43,636 nonnegative; 11,100 forced right normalizations; 11,700 erased old shifts.

All checks passed. The constructor's marker order is retained exactly; its point-generation source is hash pinned. The universal conclusions rest on §3, not the sample count. No test exhausts the full threshold universe and no reported computation decides the requested uniformly growing-k optimum.

## 8. Handoff

The useful new closure is a global primitive-row replacement and a shorter minimum witness/search exponent. The decisive missing claim is still: every threshold optimum admits a no-wider, no-costlier representative selected from a family that is uniformly polynomially searchable in n,k. Primitive normalization, exact loop erasure, bounded witness length and target-pair determinant constraints do not establish that claim.
