# Singly exponential threshold saturation and a faster parameterized algorithm

Status: proved analytical refinement, with proof-visible independent adversarial review of the constituent arguments. The uniform polynomial(n,k) target remains OPEN. No new broad test suite was run; this note builds on the prior exact checks and supplies a self-contained small-integer-point proof.

## 1. Main conclusions

For the exact restored F2 PP threshold problem, define

    m = 6k^2,     B = 8k^2,
    S(k) = (m+1) m! B^m.

Then for every k>=2, 0<=d<k, and 0<=C<=27k^3:

    theta(k,d,C) finite  ==>  theta(k,d,C) <= S(k).

Thus finite thresholds saturate at2^{O(k^2 log k)}, independently of n. A more informative split uses the known complete constructor with exact charge c0<=6k^2 and profile(a0,b0), both<=8k^2:

* If C>=c0, theta<=max(a0,b0+d)<=9k^2.
* If C<c0 and theta is finite, theta<=S(k).

Combining saturation with normalized macro enumeration yields an exact constructive threshold algorithm in

    2^{O(k^4 log k)} poly(log(n+1))

time for compact instruction output. This replaces the preceding doubly exponential FPT factor. It is still exponential in growing k, not a polynomial-time closure. With the accepted shared-table outer theorem, the full exact recursive optimizer has a corresponding2^{O(K^4 log K)} poly(n) parameterized bound.

The parent identified the saturation target and the use of saturated XP search. The refutation lane identified the c0 budget split; this lane supplies the self-contained small-point proof, explicit constants, one-exponent-per-addition refinement, and coefficient accounting. The independent reviewer separately derived the homogenized-cone argument.

## 2. Existing results used, with applicability

1. SYMBOLIC_THRESHOLD.2026-10-15T190000.md: bounded instruction skeletons, exact signed-power clustering, prefix integrality, both exact history caps, and integer-linear pattern systems. Same F2 normalization and1/3/1 charge as this note.
2. normalform_astra/PRIMITIVE_NORMAL_FORM.2026-10-15T145600.md, with its provenance/review addendum: every complete table has a same-charge, no-wider primitive-boundary representative. An addition has the form

       Z=2^p Y_d + epsilon 2^q Y_s,  min(p,q)=0,
       Y'_d=Z/2^t,

   with primitive input rows and t the common2-valuation of Z. This is the new history-scanner bridge to an existing algebraic normal form; it is not claimed newly invented here.
3. Accepted gap-closure constructor and charge staircase: an exact repository-normalized complete table has c0<=6k^2, a0,b0<=8k^2; every feasible cap minimum has charge<=27k^3. Canonical padding is free. These imports are precisely the already accepted present-model bounds.

No external small-solution theorem or integer-programming theorem is needed for this refinement's small-point proof or final search algorithm. Cramer's rule, the determinant expansion, and elementary finite-polytope decompositions are proved or recalled below. The original cluster-to-ILP algorithm used the previously source-checked Kannan theorem; the saturated finite search here does not need to run it.

## 3. One exponent variable per primitive addition

Because Y_d and Y_s are primitive integer rows:

* If p>0, 2^pY_d is even and epsilon Y_s has an odd entry. Hence Z has an odd entry, so t=0.
* If q>0, Y_d has an odd entry and epsilon2^qY_s is even. Again t=0.
* Otherwise p=q=0, and only t can vary.

Therefore every normalized addition is represented by one of three syntactic templates:

    Q: add(d,s,epsilon,h),                   h>=1;
    P: left(d,h); add(d,s,epsilon,0),        h>=1;
    R: add(d,s,epsilon,0); right(d,h),       h>=0.

Each has exactly one exponent variable. Zero exponents can be represented by R with h=0. Negations and markers have no exponent variables. If A is the number of additions, adding the ray offset a gives total integer-variable dimension

    t_dim = A+1 <= C+1.

Completeness uses primitive boundary rows from the normal form. We do NOT require every integer solution of a syntactic template system to have primitive boundary rows. That stronger condition is unnecessary: its exact prefix integrality, marker equalities, restoration and scanner inequalities already make it an allowed complete table. It may be normalized again before finite search. Thus omission of an explicit maximal-valuation constraint creates no soundness gap.

## 4. Uncapped pattern systems have small coefficients

Consider C<c0, hence integer C<=6k^2-1. Use signed-power occurrence bound M=2^C+1 and cluster gap H=C+2, so2^H>M. Remove the truncation inequality a<=n-2. Retain a>=d, nonnegative exponent variables, and all algebraic/marker/restoration constraints.

For scanner constraints, unroll each row's max-plus recurrence at both initial vectors(0,...,0) and(0,...,0,k-1). Each history value is the maximum of finitely many integer affine forms in the exponent variables. Add each affine upper-bound inequality directly against a, or against a-d+k-1. Exact prefix integrality and invertibility imply no right-shift clipping, as proved in the earlier report. No scanner variables are introduced here.

Each path uses a given instruction exponent at most once, with coefficient+1 or-1. Its constant counts additions and negations on that path plus an initial offset, so its magnitude is <=C+k-1. The F2 recipe's first2k-1 points have dyadic exponents at most k; therefore every fixed integer target coefficient exponent is at most k(k-1)<k^2, including the actual negative reciprocal convention.

Crucially, use ADJACENT gap constraints, not a collapsed equality across an entire cluster. Their right sides have magnitude at most

    H + k^2 <= C+2+k^2 <= 7k^2+1 <= 8k^2.

The potentially exponential relative span MH is used only in finite pattern acceptance, not as an ILP constant. Difference coefficients have magnitude at most2. Scanner constraints, exponent lower bounds, and a>=d also fit coefficient/right-side bound B=8k^2. We may include h<=a, which is valid under every legal capped scan and has small coefficients.

Consequently every accepted uncapped pattern is a rational polyhedron

    P = {x in R^t_dim : x>=0, Ax<=b}

with integer coefficients satisfying |A_ij|,|b_i|<=B, and t_dim<=C+1<=m=6k^2. The number of inequalities can be huge; it will not enter the small-point bound. Lower-dimensional polyhedra are permitted.

## 5. Self-contained small-integer-point lemma

**Lemma.** Let P={x>=0:Ax<=b} in R^t, with integer A,b bounded in absolute value by B>=1. If P contains an integer point, then it contains an integer point y satisfying

    0<=y_i<=(t+1)t!B^t   for every i.

### 5.1 Vertex and recession-ray bounds

At a vertex v of P, the active constraint normals have rank t. Otherwise a nonzero direction annihilating those normals would allow sufficiently small moves in both directions, respecting all finitely many inactive strict inequalities, contradicting extremality. Select t independent active constraints. Their nonsingular integer matrix has determinant of absolute value at least1. Cramer's rule and the determinant expansion give

    0<=v_i<=D=t!B^t.

This argument includes affine equalities and lower-dimensional P: a vertex still has t independent active ambient normals.

For an extreme ray of the recession cone R={r>=0:Ar<=0}, its active homogeneous constraint normals have rank t-1. Their rank cannot reach t because the nonzero ray lies in their kernel. If it were below t-1, a second independent kernel direction would permit sufficiently small two-sided perturbations into R, contradicting ray extremality. Choose t-1 independent rows. The signed maximal minors form a nonzero integer vector in the one-dimensional kernel. Choose its sign along the ray and divide its coordinates by their gcd. This yields a primitive integer ray vector r with

    0<=r_i<=(t-1)!B^(t-1)<=D.

For t=1 the empty minor is1. The recession cone may be{0}, in which case no rays are needed.

### 5.2 Why a vertex-plus-rays decomposition exists

Homogenize:

    K={(x,s): x>=0, s>=0, Ax<=bs}.

K is a cone contained in the nonnegative orthant, hence contains no line. Its slice by sum_i x_i+s=1 is a compact polytope. Every point of a compact polytope is a convex combination of its vertices: if a point is not a vertex, move in both directions inside its minimal face until an extra constraint becomes tight; express it as a convex combination of the resulting points on smaller faces and induct on face dimension. Boundedness ensures both endpoints exist, and face dimension strictly decreases.

Vertices of this slice represent extreme rays of K. A ray with s>0 can be normalized to(v,1), and v is a vertex of P: a nontrivial convex decomposition of v in P would give a nontrivial conic decomposition of that ray. A ray with s=0 is an extreme recession ray(r,0), by the same argument. Therefore any(z,1) with z in P has a decomposition

    z = v_bar + sum_j lambda_j r_j,

where v_bar is a convex combination of vertices of P, lambda_j>=0, and each r_j is a primitive integer recession ray. The coefficients on the positive-s rays sum to1, because the homogenized s coordinate is1.

The recession contribution needs at most t rays. If more are present, a linear dependence among their vectors lets one adjust the nonnegative coefficients until at least one coefficient vanishes while the sum stays fixed. The relation has coefficients of both signs because the rays are nonzero and nonnegative. Repeat until at most t independent rays remain. This proves the needed conic reduction without a separate theorem import.

### 5.3 Remove integer multiples of rays

Apply the decomposition to any integer z in P. Define

    y = z - sum_j floor(lambda_j) r_j
      = v_bar + sum_j (lambda_j-floor(lambda_j)) r_j.

y is integer because z and all r_j are integer. It remains in P because it is a convex combination of feasible vertices plus a nonnegative recession combination. It is nonnegative. There are at most t residual ray coefficients, all<1, so

    y_i <= D + tD = (t+1)t!B^t.

This establishes the lemma, independent of the number of inequalities and without full-dimensionality assumptions.

## 6. Apply the lemma to theta

If a finite threshold witness exists with C<c0, normalize it and choose its true skeleton and true exponent-cluster signatures. The resulting uncapped pattern system contains an integer point. Section5 produces another integer point with every coordinate, including a, at most

    (t_dim+1)t_dim!B^t_dim <= (m+1)m!B^m = S(k).

The pattern's exact prefix integrality, exact markers, final identity and both history inequalities make this point a complete legal table of charge<=C and ray cap at most S(k). Thus theta<=S(k).

For C>=c0, the known constructor has canonical profile(a0,b0). The choice a*=max(a0,b0+d) has a*>=d and puts that table under cap(a*,a*-d); padding is optional for exact-profile output. Since a0,b0<=8k^2 and d<=k-1, a*<=9k^2. Our S(k) certainly exceeds this for k>=2. This proves the uniform finite-threshold bound.

The argument bounds an actual COMPLETE restored table. It does not infer global feasibility from a partial state or from a coefficient-only relaxation.

## 7. Saturated finite search: singly exponential parameter factor

Immediately return theta>n-2 if n-2<d. Otherwise let

    T = min(n-2, S(k))  if C<c0,
    T = min(n-2, a*)    if C>=c0.

Run the complete normalized macro enumeration under ray cap(T,T-d), with at most C charged macros. At a primitive state choose destination/source, sign, and p,q>=0 with min(p,q)=0, then divide by the forced valuation. Under capT each p,q<=T-1, giving O(k^2(T+1)) branches per macro. Negation adds O(k) choices. Automatically consume each newly available unconsumed exact target at its first appearance; arbitrary marker order and zero marker cost justify this. Check both PRE-division transient scanner peaks and exact identity restoration.

If no accepting word exists at T, saturation proves theta>n-2, not merely a truncated-search failure. If one exists, binary-search the cap in[d,T], retaining a realizing word. Alternatively enumerate all accepting words once and minimize their actual ray cap max(a_word,b_word+d,d).

Low budgets have C<c0<=6k^2 and log S=O(k^2 log k). Their search cost is

    (k^2(S+1))^O(C) poly(S,k)
      = 2^{O(k^4 log k)}.

High budgets have T<=9k^2 and C<=27k^3, giving2^{O(k^3 log k)}. Binary search contributes only log S=poly(k). Reading/comparing n contributes poly(log(n+1)); coefficient replay uses O(T)-bit integers, already included in the parameter factor. The returned witness exponents are bounded by T, so even expanded verification no longer depends on an arbitrarily large n.

No huge cluster-pattern enumeration or integer-programming solver is executed in this final algorithm. Those objects prove the a priori saturation bound; the practical definition of the exact algorithm is finite normalized word search. The worst-case parameter exponent remains too large to imply uniform P.

## 8. Why polynomial saturation has not been proved

Small coefficients alone do not imply a polynomial coordinate bound. For example nonnegative integer constraints x1=1, x2=1, x_(i+2)=x_(i+1)+x_i have coefficients and constants in{-1,0,1} but force Fibonacci-sized coordinates, exponential in the number of variables. This is a counterexample to the GENERIC polyhedral inference only; it is not an embedding into a necessary F2 optimum and is not a lower bound on theta.

Actual F2 structure might force polynomial saturation, but that would require an additional argument using complete-table replacement, the special target set, or stronger cancellation structure. Even a polynomial saturation bound, by itself, leaves exponentially many charged skeletons and does not establish polynomial-time synthesis. The explicit remaining uniform-P problem is therefore both structural: bound/organize useful exponent patterns AND optimize complete arbitrary-helper words without exponential enumeration.

## 9. Review and artifact status

The refutation lane independently checked the small-point decomposition, the low/high budget split, and the singly exponential search consequence. The independent reviewer separately derived a homogenized-cone proof that handles lower-dimensional systems and confirmed the one-exponent parity refinement. Both emphasized that boundary primitiveness need not be imposed on every ILP solution; Section3 states this explicitly.

This is proof-visible independent review, not blind HG7. No new full synthesis implementation or universal empirical test is claimed. Existing sources remain untouched. The prior doubly exponential FPT report remains a correct earlier upper bound; this new timestamped note is the sharper continuation.
