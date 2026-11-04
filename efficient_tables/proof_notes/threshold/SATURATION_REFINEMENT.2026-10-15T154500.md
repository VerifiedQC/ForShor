# Saturation refinement and the remaining large-shift obligation

Status: analytical continuation after the first review. This is not a uniform polynomial synthesis theorem. It supplies a sharper consequence of the symbolic small-solution route and an explicit limitation of a generic polynomial-small-solution argument.

## 1. A parameter-only saturation bound is available, but exponential

The algorithm lane proposed the following elementary polyhedral lemma. If P={x>=0:Ax<=b} has an integer point, has t variables, and all integer coefficients and right sides have magnitude<=B (B>=1), it has an integer point with every coordinate at most (t+1)t!B^t. The bound does not depend on the number of inequalities.

Independent proof check: the nonnegative orthant makes P pointed. Write an integer point as a convex combination of vertices plus a nonnegative combination of extreme recession rays. Conic Carathéodory reduces the latter to at most t rays. Cramer bounds every vertex coordinate by t!B^t. Choose primitive integer ray vectors; rank-(t−1) minors bound their coordinates by (t−1)!B^(t−1). Subtract the integer parts of the ray coefficients times these integer rays from the original integer point. The remainder is integer, stays in P, and is a convex combination of the vertices plus fewer than one copy of each retained ray. This proves the displayed bound. A bounded P simply has no ray contribution.

For the symbolic threshold formulation, include a as a variable, drop the external n cutoff, and unroll the scanner maxima into affine path inequalities. Their constants and coefficients depend polynomially on k and C, not on n. The normalized macro shapes need at most two exponent variables per addition: e>=0 uses add exponent q and right-normalization exponent t; e<0 uses destination left exponent p and an add of exponentzero, with no right normalization because the source is primitive and p>0. Thus the dimension is at most2C+1. It would be incorrect to count a general independent left/add/right triple as only two variables without this case split.

This already yields the algorithm lane's finite-threshold bound2^{O(k^3 log k)} from C<=27k^3. It bounds the minimum feasible offset, not every possible witness's shifts.

## 2. The constructor budget split sharpens saturation to2^{O(k^2 log k)}

Let the already accepted paired constructor have charge c0(k)<=6k^2 and profile offsets a0,b0<=8k^2. For every kink0<=d<k, padding gives a complete table at

    a*=max(a0,b0+d)<9k^2

with charge c0. Therefore every budget C>=c0 already has theta(k,d,C)<=a*. There is no need to apply a large-charge small-solution estimate for saturation at such budgets.

Only C<c0 can have an unknown later finite threshold. These budgets satisfy C<6k^2. Primitive normalization then gives O(k^2) charged/syntax length and at most t=2C+1=O(k^2) exponent/offset variables. Use the occurrence bound M=2^C+1 and gap H=C+2. The target exponents are O(k log k), and scanner path constants are O(C+k); all matrix coefficients and right sides are bounded by some fixed polynomial in k. Applying the small-solution lemma gives

    every finite theta(k,d,C) <= 2^{O(k^2 log k)}.

This is a universal k-only saturation bound for the present F2 thresholds, conditional only on the already reviewed symbolic-system reduction and this small-solution lemma. It is exponentially larger than a polynomial in k. High budgets are covered by the actual constructor, not by an assumption that the optimum must use that constructor. Low-budget systems still allow every legal helper/order choice.

The split does not allow replacing C by c0 when computing the exact threshold at smaller offsets: extra charge can conceivably buy a narrower table. It is used only to upper-bound where a finite threshold can first occur.

## 3. Why naive cluster compression does not prove polynomial saturation

In each monomial exponent, an instruction's exponent variable has a fixed sign across all occurrences: positive for left/add shifts and negative for right shifts, and magnitude at mostone on any directed expansion path. Exponent differences consequently have coefficients in{−1,0,1}. This is a genuine structural property, but it does not by itself imply polynomially bounded integer solutions.

For example, abstract scalar equations

    2^{x1}=2,  2^{x2}=2,
    2^{x(j+2)}=2^{x(j+1)+xj},  j=1,...,m−2

give x1=x2=1 and the Fibonacci recurrence. Each equation has only two signed power occurrences; each affine exponent uses nonnegative coefficients0 or1; the cancellation cluster uses internal gapzero. Yet xm=F_m grows exponentially in m. Thus bounded occurrence count, fixed-sign variable incidence and small gap constants alone cannot prove a polynomial small-solution theorem for the accepted symbolic systems.

These are abstract symbolic constraints, not a constructed F2 table and not a hardness reduction. In particular, no claim is made that this recurrence is forced by an actual globally optimal complete table. A legal-program specialization would have to respect the shared directed-path structure of all scalar constraints and show that no alternative skeleton avoids the large solution. That is precisely the distinction the previous partial-state Newton obstruction cannot supply.

## 4. Precise remaining whole-table lemma

A sufficient new saturation lemma would say: for every complete F2 table of charge<C0(k), there exists a complete table of no greater charge whose canonical cap is at most the original cap componentwise and whose useful shift exponents are bounded by polynomial(k). Equivalently for threshold purposes, it is enough to prove that every finite threshold has some minimizing-charge-or-budget-feasible representative below a polynomial(k) offset. The second statement is weaker than preserving each supplied witness's profile and should not silently be replaced by the stronger one.

Potential proof target: show that whenever all accepted cluster patterns for a skeleton force a large scale, the complete marked/restored word can be replaced by a different skeleton at no greater charge and cap. The arbitrary row-sharing and marker obligations make this a global replacement statement; simply collapsing numerical gaps in individual scalar expressions can make the rowwise shift exponents inconsistent across coordinates.

Even a proof of polynomial saturation would not alone establish uniform P: enumeration of polynomial-length operation skeletons or bounded-coefficient helper matrices is still exponential in growing k. A separate polynomial search/optimization theorem would remain necessary.

No polynomial saturation proof or counterexample for actual complete F2 thresholds was obtained in this continuation. No hardness or non-P conclusion is drawn. No new cap graphs were launched.
